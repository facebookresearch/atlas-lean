# Row reduction of a labelled triangular grid

Let $K$ be a field and let $T$ be a labelling
that assigns a value $T_{r,d,e} \in K$ to the edge $e$ (left $L$, right $R$ or base $B$) of the
upright triangle in row $r$ (from the top) and diagonal $d$ (from the left); write $T_{r,d}$ for
that triangle and $\Delta(x, y, z) = xy/(x + y + z)$ for the delta-wye resistance function. The
reduced labelling $T'$ is given by $T'_{r,1,L} = \mathcal{P}(T_{r,1}, T_{r+1,1})$ and
$T'_{r,d,L} = \mathcal{L}(T_{r,d-1}, T_{r,d}, T_{r+1,d})$ for $d \ne 1$, where $\mathcal{P}$ is the
left-perimeter function and $\mathcal{L}$ the left-edge function; by $T'_{r,r,R}$ equal to the
bottom-right arm $\Delta(R, B, L)$ of $T_{r,r}$ plus the top arm $\Delta(L, R, B)$ of
$T_{r+1,r+1}$, and $T'_{r,d,R} = \mathcal{R}(T_{r,d}, T_{r,d+1}, T_{r+1,d+1})$ for $d \ne r$, where
$\mathcal{R}$ is the right-edge function; and by
$T'_{r,d,B} = \mathcal{B}(T_{r+2,d+1}, T_{r+1,d}, T_{r+1,d+1})$, where $\mathcal{B}$ is the
base-edge function.

Here $r$ and $d$ range over all natural numbers, with $d - 1$ truncated at $0$; only the values
with $1 \le d \le r$ are meaningful.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, Section 2 (row reduction, equations (2.2)-(2.5)).
