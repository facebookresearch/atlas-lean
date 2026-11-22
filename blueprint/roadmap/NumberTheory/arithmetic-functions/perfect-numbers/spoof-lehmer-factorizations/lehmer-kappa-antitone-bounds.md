# Bounds and monotonicity of the Lehmer function

For real numbers $t_1, \dots, t_r$ let
$\kappa_r(t_1, \dots, t_r) = (t_1 \cdots t_r - 1) / ((t_1 - 1) \cdots (t_r - 1))$. Let $r \ge 2$
and let $t_1, \dots, t_r \ge 2$ be real numbers. Then
$1 < \kappa_r(t_1, \dots, t_r) \le 2^r - 1$. Moreover, for every index $j$ and every real
$y > t_j$, replacing $t_j$ by $y$ strictly decreases $\kappa_r$, that is,
$\kappa_r(t_1, \dots, t_{j-1}, y, t_{j+1}, \dots, t_r) < \kappa_r(t_1, \dots, t_r)$.

The hypothesis $r \ge 2$ is needed: $\kappa_1(t) = 1$ for every $t \ge 2$, so for $r = 1$ the
lower bound fails and $\kappa_1$ is not strictly decreasing.

## Sources

- Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026), Article A33, Theorem 5.
