# Reduced circuit grids

Let $K$ be a field, and for each $m$ let either a boundary value
$\beta_m \in K$ be given or none. The labellings $T^m$, which assign a value $T^m_{r,d,e} \in K$ to
the edge $e$ (left $L$, right $R$ or base $B$) of the upright triangle in row $r$ and diagonal $d$,
are defined by recursion on $m$: $T^0$ is identically $1$, and $T^{m+1}$ is the row reduction of
$T^m$, except that if $\beta_{m+1}$ is given then every left edge with $d = 1$ and every right edge
with $d = r$ takes the value $\beta_{m+1}$.

With no boundary values given this is the numerical reduction of the all-one grid; in
Definitions 2.4 and 2.5 the boundary values are variables.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, Section 2 (reductions `T^m`, Definitions 2.4 and 2.5).
