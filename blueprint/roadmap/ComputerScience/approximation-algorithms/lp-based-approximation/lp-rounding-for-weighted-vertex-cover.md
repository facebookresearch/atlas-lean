# LP rounding for weighted vertex cover

For a graph $G = (V, E)$ with weights $w \ge 0$, let $x^*$ be an optimal solution of the linear program minimizing $\sum_v w_v x_v$ subject to $x_u + x_v \ge 1$ for every edge $uv$ and $0 \le x \le 1$, with value $\mathrm{LP}^*$. Then $C = \{v : x^*_v \ge 1/2\}$ is a vertex cover with $w(C) \le 2\,\mathrm{LP}^* \le 2\,\mathrm{OPT}$. Moreover the linear program has an optimal solution with all entries in $\{0, 1/2, 1\}$.

## Depends on

- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Executable graph representations and size measures (proof prerequisite; not yet stated)
- The statement must be checked against the cited sources, which have not been opened

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011
