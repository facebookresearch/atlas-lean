# Complementary slackness and the feasibility–boundedness trichotomy

For the primal $\max\{c^{\mathsf T}x : Ax \le b,\ x \ge 0\}$ and the dual $\min\{b^{\mathsf T}y : A^{\mathsf T}y \ge c,\ y \ge 0\}$: (i) feasible $x, y$ have $c^{\mathsf T}x = b^{\mathsf T}y$ if and only if $y_i(b - Ax)_i = 0$ for every $i$ and $x_j(A^{\mathsf T}y - c)_j = 0$ for every $j$; (ii) if the primal is unbounded the dual is infeasible, and if the dual is unbounded the primal is infeasible; (iii) if both are feasible, both optima are attained and equal; (iv) if the primal is infeasible and the dual feasible, the dual is unbounded. Both problems can be infeasible at once. Proof of (i): $b^{\mathsf T}y - c^{\mathsf T}x = y^{\mathsf T}(b - Ax) + x^{\mathsf T}(A^{\mathsf T}y - c)$ is a sum of nonnegative terms.

## Proof depends on

- [Strong linear programming duality](strong-linear-programming-duality.md): part (iii).
- [Weak duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md): part (ii).

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Farkas alternative for the dual system, used in part (iv).

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.2.4 (linear programs: strong duality unless both problems are infeasible) and §5.5.2 (complementary slackness)
- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, Theorem 2.6 and Corollary 2.6a
