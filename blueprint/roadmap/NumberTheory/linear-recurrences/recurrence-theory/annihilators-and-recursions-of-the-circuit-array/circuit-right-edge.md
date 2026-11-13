# Right-edge function

Let $K$ be a field, let $\Delta(x, y, z) = xy/(x + y + z)$ and
$Y(a, b, c) = (ab + bc + ca)/a$ be the delta-wye and wye-delta resistance functions, and for an
upright triangle $t$ write $L_t$, $R_t$, $B_t \in K$ for the values on its left, right and base
edges. For triangles $t$, $u$, $v$, the right-edge function is
$\mathcal{R}(t, u, v) = Y(\Delta(B_u, L_u, R_u), \Delta(R_t, B_t, L_t), \Delta(L_v, R_v, B_v))$,
the wye-delta transform of the star formed by the bottom-left arm of $u$, the bottom-right arm of
$t$ and the top arm of $v$, with the arm of $u$ first.

In the row reduction of a labelling $T$ it is applied to $t = T_{r,d}$, $u = T_{r,d+1}$ and
$v = T_{r+1,d+1}$ for $d \ne r$, where $T_{r,d}$ is the triangle in row $r$ and diagonal $d$. This
follows Steps 2-5 and Figure 2; the displayed equation (2.4) instead uses $T_{r+1,d}$ in place of
$T_{r+1,d+1}$ and puts the arm of $t$ first, which gives $C_{1,2} = 29/36$ against Table 1's
$13/12$.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, equation (2.4) (corrected as above).
