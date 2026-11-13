# Left-edge function

Let $K$ be a field, let $\Delta(x, y, z) = xy/(x + y + z)$ and
$Y(a, b, c) = (ab + bc + ca)/a$ be the delta-wye and wye-delta resistance functions, and for an
upright triangle $t$ write $L_t$, $R_t$, $B_t \in K$ for the values on its left, right and base
edges. For triangles $t$, $u$, $v$, the left-edge function is
$\mathcal{L}(t, u, v) = Y(\Delta(R_t, B_t, L_t), \Delta(B_u, L_u, R_u), \Delta(L_v, R_v, B_v))$,
the wye-delta transform of the star formed by the bottom-right arm of $t$, the bottom-left arm of
$u$ and the top arm of $v$, with the arm of $t$ first.

In the row reduction of a labelling $T$ it is applied to $t = T_{r,d-1}$, $u = T_{r,d}$ and
$v = T_{r+1,d}$ for $d \ne 1$, where $T_{r,d}$ is the triangle in row $r$ and diagonal $d$.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, equation (2.5).
