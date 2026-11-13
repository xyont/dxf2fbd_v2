/* --------------------------------------------------------------------   */
/*                           CALCULIX                                      */
/*                    - GRAPHICAL INTERFACE -                              */
/*                                                                         */
/*      readDxf.c - DXF to FBD Converter for CalculiX CGX                  */
/*      Generates .fbd file with PNT, LINE, CURVE, and GSUR definitions    */
/*      Based on dxf2fbd.cpp by David Colignon & Suyono Nt.                  */
/*      Modified to support automatic GSUR generation from closed loops    */
/*      All comments in English. 3DFACE support removed.                   */
/* --------------------------------------------------------------------   */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define DEG2RAD      (M_PI/180.0)
#define BUFSIZE      2048
#define GEOLINE      1
#define GEOCIRCLE    2
#define MAXPTS       100000
#define MAXCRV       100000
#define MAXSUR       10000
#define MAXTEMP      50000
#define THETOL_DEF   1e-6f

/* Global state for DXF parsing */
static FILE *infile, *outfile;
static char inname[256], outname[256], curobj[256], linbuf[BUFSIZE];
static int groupcode, curcolor;
static int ints[10], nump = 1, numc = 1, nums = 1;
static float xcoords[10], ycoords[10], zcoords[10];
static float floats_[10], angles[10];
static float extru[3] = {0.0f, 0.0f, 1.0f};
static float THETOL = THETOL_DEF;
static int LDIV = 4; /* Default division for lines/arcs */

/* Counters for report */
static int count_points = 0;
static int count_lines = 0;
static int count_curves = 0;
static int count_surfaces = 0;

/* Data structures for Points and Curves */
typedef struct {
    int   num;
    float x, y, z;
} Point;

typedef struct {
    int num;
    int type; /* 1=Line, 2=Arc/Circle */
    int a, b, c; /* For Line: a=start, b=end. For Arc: a=start, b=center, c=end */
} Curve;

typedef struct {
    int num;
    int n_lines;
    int line_indices[10]; /* Indices of curves forming this surface */
    int directions[10];   /* 1 or -1 for direction */
} Surface;

static Point Point_T[MAXPTS];
static int   Point_N = 0;
static Curve Curve_T[MAXCRV];
static int   Curve_N = 0;
static Surface Surf_T[MAXSUR];
static int   Surf_N = 0;

/* Temporary storage for detecting closed loops */
typedef struct {
    int c_idx; /* Index in Curve_T */
    int n1, n2; /* Node indices */
    float x1, y1, z1;
    float x2, y2, z2;
    int used;
} TempLine;

static TempLine *Temp_Lines = NULL;
static int Num_Temp_Lines = 0;

/* Forward declarations */
static int getline_dxf(FILE *handle);
static int point_equal(float x1, float y1, float z1, float x2, float y2, float z2);
static void buildAxes(const float N[3], float U[3], float V[3]);
static void arcPoint(float cx, float cy, float cz, float R, const float U[3], const float V[3], float theta, float *px, float *py, float *pz);
static int addpoint(float x, float y, float z);
static void addcurve(int type, int a, int b, int c);
static void add_temp_line(int c_idx, int n1, int n2, float x1, float y1, float z1, float x2, float y2, float z2);
static void find_closed_loops_and_add_gsur();
static void write_fbd();

/* ==================================================================== */
/* HELPER FUNCTIONS FOR SPLIT & MERGE NODE                              */
/* ==================================================================== */

static int get_intersection_3d(float x1, float y1, float z1, float x2, float y2, float z2,
                        float x3, float y3, float z3, float x4, float y4, float z4,
                        float *ix, float *iy, float *iz) 
{
    double p1[3] = {x1, y1, z1};
    double p2[3] = {x2, y2, z2};
    double p3[3] = {x3, y3, z3};
    double p4[3] = {x4, y4, z4};
    
    double d1[3], d2[3], r[3];
    int k;
    for(k=0; k<3; k++) {
        d1[k] = p2[k] - p1[k]; 
        d2[k] = p4[k] - p3[k]; 
        r[k]  = p1[k] - p3[k]; 
    }
    
    double a = d1[0]*d1[0] + d1[1]*d1[1] + d1[2]*d1[2];
    double b = d1[0]*d2[0] + d1[1]*d2[1] + d1[2]*d2[2];
    double c = d2[0]*d2[0] + d2[1]*d2[1] + d2[2]*d2[2];
    double d = d1[0]*r[0]  + d1[1]*r[1]  + d1[2]*r[2];
    double e = d2[0]*r[0]  + d2[1]*r[1]  + d2[2]*r[2];
    
    double denom = a*c - b*b;
    if (fabs(denom) < 1e-9) return 0; 
    
    double s = (a*e - b*d) / denom;
    double t = (b*e - c*d) / denom;
    
    if (t >= 0.0 && t <= 1.0 && s >= 0.0 && s <= 1.0) {
        double ix_d = p1[0] + t * d1[0];
        double iy_d = p1[1] + t * d1[1];
        double iz_d = p1[2] + t * d1[2];
        
        double cx = p3[0] + s * d2[0];
        double cy = p3[1] + s * d2[1];
        double cz = p3[2] + s * d2[2];
        
        if (fabs(ix_d - cx) < 1e-4 && fabs(iy_d - cy) < 1e-4 && fabs(iz_d - cz) < 1e-4) {
            *ix = (float)ix_d;
            *iy = (float)iy_d;
            *iz = (float)iz_d;
            return 1; 
        }
    }
    return 0; 
}

static int is_angle_between(float ang, float ang_s, float ang_e) {
    while (ang < 0) ang += 2.0f * (float)M_PI;
    while (ang_s < 0) ang_s += 2.0f * (float)M_PI;
    while (ang_e < 0) ang_e += 2.0f * (float)M_PI;

    if (ang_s <= ang_e) {
        return (ang >= ang_s - 1e-5f && ang <= ang_e + 1e-5f);
    } else {
        return (ang >= ang_s - 1e-5f || ang <= ang_e + 1e-5f);
    }
}

static void split_lines_3d() {
    int i, j;
    int original_curve_N = Curve_N; 
    
    for (i = 0; i < original_curve_N; i++) {
        if (Curve_T[i].type != GEOLINE) continue;
        
        for (j = i + 1; j < original_curve_N; j++) {
            if (Curve_T[j].type != GEOLINE) continue;
            
            int n1 = Curve_T[i].a, n2 = Curve_T[i].b;
            int n3 = Curve_T[j].a, n4 = Curve_T[j].b;
            
            float ix, iy, iz;
            if (get_intersection_3d(
                    Point_T[n1-1].x, Point_T[n1-1].y, Point_T[n1-1].z,
                    Point_T[n2-1].x, Point_T[n2-1].y, Point_T[n2-1].z,
                    Point_T[n3-1].x, Point_T[n3-1].y, Point_T[n3-1].z,
                    Point_T[n4-1].x, Point_T[n4-1].y, Point_T[n4-1].z,
                    &ix, &iy, &iz)) 
            {
                if (point_equal(Point_T[n1-1].x, Point_T[n1-1].y, Point_T[n1-1].z, ix, iy, iz) ||
                    point_equal(Point_T[n2-1].x, Point_T[n2-1].y, Point_T[n2-1].z, ix, iy, iz) ||
                    point_equal(Point_T[n3-1].x, Point_T[n3-1].y, Point_T[n3-1].z, ix, iy, iz) ||
                    point_equal(Point_T[n4-1].x, Point_T[n4-1].y, Point_T[n4-1].z, ix, iy, iz)) {
                    continue;
                }

                int inode = addpoint(ix, iy, iz);
                
                Curve_T[i].b = inode;
                addcurve(GEOLINE, inode, n2, 0);
                
                Curve_T[j].b = inode;
                addcurve(GEOLINE, inode, n4, 0);
            }
        }
    }
}

static void split_line_arcs_ortho() {
    int i, j, k;
    int orig_line_N = Curve_N;
    
    for (i = 0; i < orig_line_N; i++) {
        if (Curve_T[i].type != GEOLINE) continue;
        
        for (j = 0; j < orig_line_N; j++) {
            if (Curve_T[j].type != GEOCIRCLE) continue;
            
            int ln1 = Curve_T[i].a, ln2 = Curve_T[i].b;
            int as = Curve_T[j].a, ac = Curve_T[j].b, ae = Curve_T[j].c;
            
            float x1 = Point_T[ln1-1].x, y1 = Point_T[ln1-1].y, z1 = Point_T[ln1-1].z;
            float x2 = Point_T[ln2-1].x, y2 = Point_T[ln2-1].y, z2 = Point_T[ln2-1].z;
            float cx = Point_T[ac-1].x, cy = Point_T[ac-1].y, cz = Point_T[ac-1].z;
            float sx = Point_T[as-1].x, sy = Point_T[as-1].y, sz = Point_T[as-1].z;
            float ex = Point_T[ae-1].x, ey = Point_T[ae-1].y, ez = Point_T[ae-1].z;
            
            float R = (float)sqrt((sx-cx)*(sx-cx) + (sy-cy)*(sy-cy) + (sz-cz)*(sz-cz));
            
            float p1u, p1v, p2u, p2v, cu, cv, su, sv, eu, ev;
            float ix, iy, iz;
            int is_xy = 0, is_xz = 0;
            
            if (fabs(z1 - cz) < 1e-4 && fabs(z2 - cz) < 1e-4) { 
                is_xy = 1;
                p1u = x1; p1v = y1; p2u = x2; p2v = y2;
                cu = cx; cv = cy; su = sx; sv = sy; eu = ex; ev = ey;
            } else if (fabs(y1 - cy) < 1e-4 && fabs(y2 - cy) < 1e-4) { 
                is_xz = 1;
                p1u = x1; p1v = z1; p2u = x2; p2v = z2;
                cu = cx; cv = cz; su = sx; sv = sz; eu = ex; ev = ez;
            } else if (fabs(x1 - cx) < 1e-4 && fabs(x2 - cx) < 1e-4) { 
                p1u = y1; p1v = z1; p2u = y2; p2v = z2;
                cu = cy; cv = cz; su = sy; sv = sz; eu = ey; ev = ez;
            } else {
                continue; 
            }
            
            float dx = p2u - p1u;
            float dy = p2v - p1v;
            float a = dx*dx + dy*dy;
            if (a < 1e-9f) continue; 
            
            float b = 2.0f * (dx*(p1u - cu) + dy*(p1v - cv));
            float c = (p1u - cu)*(p1u - cu) + (p1v - cv)*(p1v - cv) - R*R;
            
            float D = b*b - 4*a*c;
            if (D < 0) continue; 
            
            float sqrtD = (float)sqrt(D);
            float t1 = (-b - sqrtD) / (2*a);
            float t2 = (-b + sqrtD) / (2*a);
            
            float t_vals[2] = {t1, t2};
            for (k = 0; k < 2; k++) {
                float t = t_vals[k];
                
                if (t >= 0.0f && t <= 1.0f) {
                    float iu = p1u + t * dx;
                    float iv = p1v + t * dy;
                    
                    float ang_i = atan2(iv - cv, iu - cu);
                    float ang_s = atan2(sv - cv, su - cu);
                    float ang_e = atan2(ev - cv, eu - cu);
                    
                    if (is_angle_between(ang_i, ang_s, ang_e)) {
                        if (t < 1e-4f || t > 1.0f - 1e-4f) continue;
                        
                        if (is_xy) { ix = iu; iy = iv; iz = cz; }
                        else if (is_xz) { ix = iu; iy = cy; iz = iv; }
                        else { ix = cx; iy = iu; iz = iv; }
                        
                        int inode = addpoint(ix, iy, iz);
                        
                        Curve_T[i].b = inode;
                        addcurve(GEOLINE, inode, ln2, 0);
                        
                        Curve_T[j].c = inode; 
                        addcurve(GEOCIRCLE, inode, ac, ae); 
                        
                        break; 
                    }
                }
            }
        }
    }
}

/* Update Temp_Lines after split process for accurate GSUR detection */
static void rebuild_temp_lines() {
    int i;
    Num_Temp_Lines = 0;
    for (i = 0; i < Curve_N; i++) {
        if (Curve_T[i].type == GEOLINE) {
            int n1 = Curve_T[i].a;
            int n2 = Curve_T[i].b;
            add_temp_line(i, n1, n2,
                          Point_T[n1-1].x, Point_T[n1-1].y, Point_T[n1-1].z,
                          Point_T[n2-1].x, Point_T[n2-1].y, Point_T[n2-1].z);
        }
    }
}
/* ==================================================================== */

/*
 * Read one pair (groupcode, value) from DXF file
 */
static int getline_dxf(FILE *handle)
{
    if (!fgets(linbuf, BUFSIZE, handle)) return 1;
    if (feof(handle)) return 1;
    if (sscanf(linbuf, "%3d", &groupcode) != 1) return 1;
    if (!fgets(linbuf, BUFSIZE, handle)) return 1;
    if (feof(handle)) return 1;
    return 0;
}

/*
 * Check equality of two points with tolerance
 */
static int point_equal(float x1, float y1, float z1, float x2, float y2, float z2)
{
    return (fabsf(x1 - x2) <= THETOL &&
            fabsf(y1 - y2) <= THETOL &&
            fabsf(z1 - z2) <= THETOL);
}

/*
 * Arbitrary Axis Algorithm (AutoCAD)
 * Build local axes U,V from normal N
 */
static void buildAxes(const float N[3], float U[3], float V[3])
{
    float n[3];
    float len, alen;
    float Ax[3];
    const float TOL64 = 1.0f / 64.0f;
    
    n[0] = N[0]; n[1] = N[1]; n[2] = N[2];
    len = (float)sqrt((double)(n[0]*n[0] + n[1]*n[1] + n[2]*n[2]));
    
    if (len < 1e-12f) { 
        n[0] = 0.0f; n[1] = 0.0f; n[2] = 1.0f; 
        len = 1.0f; 
    }
    
    n[0] /= len; n[1] /= len; n[2] /= len;
    
    if (fabsf(n[0]) < TOL64 && fabsf(n[1]) < TOL64) {
        /* Wy x N = (Nz, 0, -Nx) */
        Ax[0] =  n[2];
        Ax[1] =  0.0f;
        Ax[2] = -n[0];
    } else {
        /* Wz x N = (-Ny, Nx, 0) */
        Ax[0] = -n[1];
        Ax[1] =  n[0];
        Ax[2] =  0.0f;
    }
    
    alen = (float)sqrt((double)(Ax[0]*Ax[0] + Ax[1]*Ax[1] + Ax[2]*Ax[2]));
    U[0] = Ax[0] / alen;
    U[1] = Ax[1] / alen;
    U[2] = Ax[2] / alen;
    
    /* V = N x U */
    V[0] = n[1]*U[2] - n[2]*U[1];
    V[1] = n[2]*U[0] - n[0]*U[2];
    V[2] = n[0]*U[1] - n[1]*U[0];
}

/*
 * Calculate point on 3D arc
 */
static void arcPoint(float cx, float cy, float cz, float R,
                     const float U[3], const float V[3],
                     float theta, float *px, float *py, float *pz)
{
    float c = (float)cos((double)theta);
    float s = (float)sin((double)theta);
    *px = cx + R * (c * U[0] + s * V[0]);
    *py = cy + R * (c * U[1] + s * V[1]);
    *pz = cz + R * (c * U[2] + s * V[2]);
}

/*
 * Add point to array, perform deduplication
 * Returns: point number
 */
static int addpoint(float x, float y, float z)
{
    int i;
    for (i = 0; i < Point_N; i++) {
        if (point_equal(Point_T[i].x, Point_T[i].y, Point_T[i].z, x, y, z)) {
            return Point_T[i].num;
        }
    }
    
    if (Point_N >= MAXPTS) {
        printf("ERROR: Point_T overflow\n");
        exit(1);
    }
    
    Point_T[Point_N].num = nump++;
    Point_T[Point_N].x = x;
    Point_T[Point_N].y = y;
    Point_T[Point_N].z = z;
    Point_N++;
    count_points++;
    
    return Point_T[Point_N-1].num;
}

/*
 * Add curve to array
 */
static void addcurve(int type, int a, int b, int c)
{
    if (Curve_N >= MAXCRV) {
        printf("ERROR: Curve_T overflow\n");
        exit(1);
    }
    
    Curve_T[Curve_N].num = numc++;
    Curve_T[Curve_N].type = type;
    Curve_T[Curve_N].a = a;
    Curve_T[Curve_N].b = b;
    Curve_T[Curve_N].c = c;
    Curve_N++;
    
    if (type == 1) count_lines++;
    else if (type == 2) count_curves++;
}

/*
 * Add line to temporary array for closed loop detection
 */
static void add_temp_line(int c_idx, int n1, int n2, float x1, float y1, float z1, float x2, float y2, float z2)
{
    if (Num_Temp_Lines >= MAXTEMP) {
        return; 
    }
    
    Temp_Lines[Num_Temp_Lines].c_idx = c_idx;
    Temp_Lines[Num_Temp_Lines].n1 = n1;
    Temp_Lines[Num_Temp_Lines].n2 = n2;
    Temp_Lines[Num_Temp_Lines].x1 = x1;
    Temp_Lines[Num_Temp_Lines].y1 = y1;
    Temp_Lines[Num_Temp_Lines].z1 = z1;
    Temp_Lines[Num_Temp_Lines].x2 = x2;
    Temp_Lines[Num_Temp_Lines].y2 = y2;
    Temp_Lines[Num_Temp_Lines].z2 = z2;
    Temp_Lines[Num_Temp_Lines].used = 0;
    Num_Temp_Lines++;
}

/*
 * Find closed loops of 4 lines and add GSUR
 */
static void find_closed_loops_and_add_gsur()
{
    int i, j, k, l;
    int found_loop = 0;
    
    printf("\nSearching for closed loops of 4 lines to generate GSUR...\n");
    
    for (i = 0; i < Num_Temp_Lines; i++) {
        Temp_Lines[i].used = 0;
    }
    
    for (i = 0; i < Num_Temp_Lines; i++) {
        if (Temp_Lines[i].used) continue;
        
        for (j = 0; j < Num_Temp_Lines; j++) {
            if (j == i || Temp_Lines[j].used) continue;
            
            if (!point_equal(Temp_Lines[i].x2, Temp_Lines[i].y2, Temp_Lines[i].z2,
                            Temp_Lines[j].x1, Temp_Lines[j].y1, Temp_Lines[j].z1)) {
                continue;
            }
            
            for (k = 0; k < Num_Temp_Lines; k++) {
                if (k == i || k == j || Temp_Lines[k].used) continue;
                
                if (!point_equal(Temp_Lines[j].x2, Temp_Lines[j].y2, Temp_Lines[j].z2,
                                Temp_Lines[k].x1, Temp_Lines[k].y1, Temp_Lines[k].z1)) {
                    continue;
                }
                
                for (l = 0; l < Num_Temp_Lines; l++) {
                    if (l == i || l == j || l == k || Temp_Lines[l].used) continue;
                    
                    if (point_equal(Temp_Lines[k].x2, Temp_Lines[k].y2, Temp_Lines[k].z2,
                                   Temp_Lines[l].x1, Temp_Lines[l].y1, Temp_Lines[l].z1) &&
                        point_equal(Temp_Lines[l].x2, Temp_Lines[l].y2, Temp_Lines[l].z2,
                                   Temp_Lines[i].x1, Temp_Lines[i].y1, Temp_Lines[i].z1)) {
                        
                        if (Surf_N < MAXSUR) {
                            Surf_T[Surf_N].num = nums++;
                            Surf_T[Surf_N].n_lines = 4;
                            Surf_T[Surf_N].line_indices[0] = Temp_Lines[i].c_idx;
                            Surf_T[Surf_N].line_indices[1] = Temp_Lines[j].c_idx;
                            Surf_T[Surf_N].line_indices[2] = Temp_Lines[k].c_idx;
                            Surf_T[Surf_N].line_indices[3] = Temp_Lines[l].c_idx;
                            
                            Surf_T[Surf_N].directions[0] = 1;
                            Surf_T[Surf_N].directions[1] = 1;
                            Surf_T[Surf_N].directions[2] = 1;
                            Surf_T[Surf_N].directions[3] = 1;
                            
                            Surf_N++;
                            count_surfaces++;
                            
                            Temp_Lines[i].used = 1;
                            Temp_Lines[j].used = 1;
                            Temp_Lines[k].used = 1;
                            Temp_Lines[l].used = 1;
                            
                            printf(" Found closed loop for GSUR A%03d\n", Surf_T[Surf_N-1].num);
                        }
                        
                        found_loop = 1;
                        break;
                    }
                }
                if (found_loop) { found_loop = 0; break; }
            }
        }
    }
    
    printf(" Generated %d GSUR elements from closed loops.\n", Surf_N);
}

/*
 * Write output to .fbd file
 */
static void write_fbd()
{
    int i, j;
    
    fprintf(outfile, "/* Converted from DXF: %s */\n", inname);
    fprintf(outfile, "/* Tolerance %g, Division %d */\n\n", THETOL, LDIV);
    
    for (i = 0; i < Point_N; i++) {
        fprintf(outfile, "PNT P%03d %12.5f %12.5f %12.5f\n", 
                Point_T[i].num, Point_T[i].x, Point_T[i].y, Point_T[i].z);
    }
    
    fprintf(outfile, "\n");
    
    for (i = 0; i < Curve_N; i++) {
        if (Curve_T[i].type == 1) { /* LINE */
            fprintf(outfile, "LINE L%03d P%03d P%03d %d\n", 
                    Curve_T[i].num, Curve_T[i].a, Curve_T[i].b, LDIV);
        } else if (Curve_T[i].type == 2) { /* ARC/CIRCLE */
            /* Correct CGX format: Start, End, Center */
            fprintf(outfile, "LINE C%03d P%03d P%03d P%03d %d\n", 
                    Curve_T[i].num, Curve_T[i].a, Curve_T[i].c, Curve_T[i].b, LDIV);
        }
    }
    
    fprintf(outfile, "\n");
    
    for (i = 0; i < Surf_N; i++) {
        fprintf(outfile, "GSUR A%03d + BLEND ", Surf_T[i].num);
        for (j = 0; j < Surf_T[i].n_lines; j++) {
            int c_num = Curve_T[Surf_T[i].line_indices[j]].num;
            int dir = Surf_T[i].directions[j];
            if (dir == 1)
                fprintf(outfile, "+ L%03d ", c_num);
            else
                fprintf(outfile, "- L%03d ", c_num);
        }
        fprintf(outfile, "\n");
    }
    
    fprintf(outfile, "\nELTY all QU4\n");
}

/*
 * Process current object
 */
static void addobj(void)
{
    /* All variable declarations at the top for C89 compatibility */
    int n1, n2, n3, n4, n5; /* n5 added */
    float cx, cy, cz, R;
    float U[3], V[3];
    float px, py, pz;
    float a0, a1, sweep, aMid;
    
    if (strstr(curobj, "POINT")) {
        addpoint(xcoords[0], ycoords[0], zcoords[0]);
    }
    else if (strstr(curobj, "LINE") || strstr(curobj, "3DLINE")) {
        if (point_equal(xcoords[0], ycoords[0], zcoords[0],
                       xcoords[1], ycoords[1], zcoords[1])) {
            return;
        }
        
        n1 = addpoint(xcoords[0], ycoords[0], zcoords[0]);
        n2 = addpoint(xcoords[1], ycoords[1], zcoords[1]);
        
        addcurve(GEOLINE, n1, n2, 0); 
        add_temp_line(Curve_N-1, n1, n2, xcoords[0], ycoords[0], zcoords[0],
                                     xcoords[1], ycoords[1], zcoords[1]);
    }
    else if (strstr(curobj, "CIRCLE")) {
        cx = xcoords[0]; cy = ycoords[0]; cz = zcoords[0];
        R = floats_[0];
        
        /* Calculate local 3D axes from normal vector (extru) */
        buildAxes(extru, U, V);
        
        /* Center point */
        n1 = addpoint(cx, cy, cz); 
        
        /* Point at 0 degrees (U axis) */
        arcPoint(cx, cy, cz, R, U, V, 0.0f, &px, &py, &pz);
        n2 = addpoint(px, py, pz); 
        
        /* Point at 90 degrees (V axis) */
        arcPoint(cx, cy, cz, R, U, V, (float)M_PI/2.0f, &px, &py, &pz);
        n3 = addpoint(px, py, pz);
        
        /* Point at 180 degrees (-U axis) */
        arcPoint(cx, cy, cz, R, U, V, (float)M_PI, &px, &py, &pz);
        n4 = addpoint(px, py, pz);
        
        /* Point at 270 degrees (-V axis) */
        arcPoint(cx, cy, cz, R, U, V, 3.0f*(float)M_PI/2.0f, &px, &py, &pz);
        n5 = addpoint(px, py, pz);
        
        /* Create 4 arcs to form a full circle (Start, Center, End) */
        addcurve(GEOCIRCLE, n2, n1, n3);
        addcurve(GEOCIRCLE, n3, n1, n4);
        addcurve(GEOCIRCLE, n4, n1, n5);
        addcurve(GEOCIRCLE, n5, n1, n2);
    }
    else if (strstr(curobj, "ARC")) {
        cx = xcoords[0]; cy = ycoords[0]; cz = zcoords[0];
        R = floats_[0];
        a0 = angles[0] * DEG2RAD;
        a1 = angles[1] * DEG2RAD;
        
        buildAxes(extru, U, V);
        
        /* Center point */
        n1 = addpoint(cx, cy, cz);
        
        /* Start point */
        arcPoint(cx, cy, cz, R, U, V, a0, &px, &py, &pz);
        n2 = addpoint(px, py, pz);
        
        /* End point */
        arcPoint(cx, cy, cz, R, U, V, a1, &px, &py, &pz);
        n3 = addpoint(px, py, pz);
        
        /* Calculate sweep angle */
        sweep = a1 - a0;
        while (sweep < 0.0f) sweep += 2.0f * (float)M_PI;
        while (sweep >= 2.0f * (float)M_PI) sweep -= 2.0f * (float)M_PI;
        
        if (sweep <= (float)M_PI + 1e-6f) {
            /* Arc <= 180 degrees */
            addcurve(GEOCIRCLE, n2, n1, n3); 
        } else {
            /* Arc > 180 degrees: split into 2 */
            aMid = a0 + sweep * 0.5f;
            arcPoint(cx, cy, cz, R, U, V, aMid, &px, &py, &pz);
            n4 = addpoint(px, py, pz);
            
            addcurve(GEOCIRCLE, n2, n1, n4);
            addcurve(GEOCIRCLE, n4, n1, n3);
        }
    }
}

/*
 * Main function: readDxf
 * Reads DXF file and generates .fbd file
 */
int readDxf(char *datin, float tol, int ldiv_val)
{
    int i;
    int found_entities = 0;
    char *ext;
    
    THETOL = tol;
    LDIV = ldiv_val;
    
    printf("readDxf: Reading DXF file for CalculiX CGX\n");
    
    Temp_Lines = (TempLine *)malloc(MAXTEMP * sizeof(TempLine));
    if (!Temp_Lines) {
        printf("\n\n ERROR: malloc failed for Temp_Lines\n\n");
        return -1;
    }
    Num_Temp_Lines = 0;
    
    strcpy(inname, datin);
    if (strchr(inname, '.') == NULL) {
        strcat(inname, ".dxf");
    }
    infile = fopen(inname, "r");
    if (!infile) {
        printf("ERROR: Cannot open %s\n", inname);
        free(Temp_Lines);
        return -1;
    }
    
    strcpy(outname, inname);
    ext = strchr(outname, '.');
    if (ext) strcpy(ext, ".fbd");
    else strcat(outname, ".fbd");
    
    outfile = fopen(outname, "w");
    if (!outfile) {
        printf("ERROR: Cannot create %s\n", outname);
        fclose(infile);
        free(Temp_Lines);
        return -1;
    }
    
    printf(" file:%s opened\n", inname);
    printf(" reading DXF format\n");
    
    for (i = 0; i < 10; i++) {
        xcoords[i] = ycoords[i] = zcoords[i] = 0.0f;
        floats_[i] = angles[i] = 0.0f;
        ints[i] = 0;
    }
    extru[0] = 0.0f; extru[1] = 0.0f; extru[2] = 1.0f;
    curobj[0] = '\0';
    
    while (!feof(infile)) {
        if (getline_dxf(infile)) break;
        
        if (groupcode == 0) {
            if (strstr(linbuf, "EOF")) break;
            if (strstr(linbuf, "SECTION")) {
                if (getline_dxf(infile)) break;
                if (groupcode == 2 && strstr(linbuf, "ENTITIES")) {
                    found_entities = 1;
                    break;
                }
            }
        }
    }
    
    if (!found_entities) {
        printf("WARNING: No ENTITIES section found in DXF file\n");
        fclose(infile);
        fclose(outfile);
        free(Temp_Lines);
        return -1;
    }
    
    while (!feof(infile)) {
        if (getline_dxf(infile)) break;
        
        if (groupcode < 10) {
            switch (groupcode) {
            case 0:  
                if (strlen(curobj) > 0) {
                    addobj();
                }
                
                if (strstr(linbuf, "EOF") || strstr(linbuf, "ENDSEC")) {
                    goto stop_reading;
                }
                
                strcpy(curobj, linbuf);
                extru[0] = 0.0f; extru[1] = 0.0f; extru[2] = 1.0f;
                
                for (i = 0; i < 10; i++) {
                    xcoords[i] = ycoords[i] = zcoords[i] = 0.0f;
                }
                break;
                
            case 62:  
                sscanf(linbuf, "%d", &curcolor);
                break;
                
            default:
                break;
            }
        }
        else if (groupcode >= 10 && groupcode < 19) {
            sscanf(linbuf, "%f", &xcoords[groupcode - 10]);
        }
        else if (groupcode >= 20 && groupcode < 29) {
            sscanf(linbuf, "%f", &ycoords[groupcode - 20]);
        }
        else if (groupcode >= 30 && groupcode < 38) {
            sscanf(linbuf, "%f", &zcoords[groupcode - 30]);
        }
        else if (groupcode >= 40 && groupcode < 49) {
            sscanf(linbuf, "%f", &floats_[groupcode - 40]);
        }
        else if (groupcode >= 50 && groupcode < 59) {
            sscanf(linbuf, "%f", &angles[groupcode - 50]);
        }
        else if (groupcode >= 70 && groupcode < 79) {
            sscanf(linbuf, "%d", &ints[groupcode - 70]);
        }
        else if (groupcode == 210) {
            sscanf(linbuf, "%f", &extru[0]);
        }
        else if (groupcode == 220) {
            sscanf(linbuf, "%f", &extru[1]);
        }
        else if (groupcode == 230) {
            sscanf(linbuf, "%f", &extru[2]);
        }
    }
    
stop_reading:
    if (strlen(curobj) > 0) {
        addobj();
    }
    
    fclose(infile);

    /* ======================================================== */
    /* CALL SPLIT FUNCTIONS & REBUILD TEMP_LINES                */
    /* ======================================================== */
    
    printf("\nSplitting intersecting 3D lines...\n");
    split_lines_3d();
    
    printf("\nSplitting orthogonal Line-Arc intersections...\n");
    split_line_arcs_ortho();
    
    /* Rebuild Temp_Lines so GSUR can be detected from split lines */
    rebuild_temp_lines();

    /* Generate GSUR from closed loops */
    find_closed_loops_and_add_gsur();
    
    /* Write output to .fbd file */
    write_fbd();
    
    fclose(outfile);
    free(Temp_Lines);
    
    /* Final Report */
    printf("\n--- Conversion Report ---\n");
printf("Points: %d | Lines: %d | Curves: %d | Surfaces: %d\n", 
       count_points, count_lines, count_curves, count_surfaces);
    printf("-------------------------\n");
    printf("DXF conversion complete: %s -> %s\n", inname, outname);
    
    return 1;
}
