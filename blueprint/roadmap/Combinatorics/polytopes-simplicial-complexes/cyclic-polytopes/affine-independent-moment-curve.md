# The moment curve has order $d$

Let $m \le d + 1$ and let $t_1, \dots, t_m$ be distinct real numbers. Then the points
$\gamma(t_1), \dots, \gamma(t_m)$ of the moment curve in $\mathbb{R}^d$ are affinely independent.
For $m = d + 1$ this says that no $d + 1$ points of the curve lie on a common affine hyperplane,
so the moment curve has order $d$ in the sense of the PCMI notes.

Proof: an affine dependence $\sum_i w_i \gamma(t_i) = 0$, $\sum_i w_i = 0$ gives
$\sum_i w_i t_i^k = 0$ for $0 \le k \le m - 1$, so $w$ is in the left kernel of the Vandermonde
matrix $(t_i^k)$, whose determinant $\prod_{i<j}(t_j - t_i)$ is nonzero.

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Example 2.6.
