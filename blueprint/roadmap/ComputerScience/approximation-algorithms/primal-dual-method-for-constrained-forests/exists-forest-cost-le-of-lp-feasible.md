# Goemans–Williamson integrality gap for proper constrained forest problems

Let $G$ be a finite simple graph with nonnegative edge costs $c$, and $f$ a
[proper](is-proper.md) requirement function with $f(V) = 0$; put $A = \{v : f(\{v\}) = 1\}$. For
every feasible solution $x \ge 0$ of the linear relaxation ($x(\delta(S)) \ge 1$ whenever
$f(S) = 1$) there is a set $F$ of edges of $G$ meeting every cut $\delta(S)$ with $f(S) = 1$ and

$$c(F) \le \left(2 - \frac{2}{|A|}\right) \sum_e c_e x_e .$$

Here $2/|A|$ is read as $0$ when $A = \emptyset$. Goemans and Williamson prove more (Theorem 2.4): their primal–dual
algorithm grows a dual solution $y$ on the active components and returns a forest $F'$ with
$c(F') \le (2 - 2/|A|) \sum_S y_S \le (2 - 2/|A|) Z^*_{LP}$, in $O(\min(n^2 \log n, mn\,\alpha(m, n)))$ time. The
statement above is the consequence they state on p. 297, that the ratio between the optimal
values of (IP) and (LP) is at most $2 - 2/|A|$. When $A = \emptyset$ the factor is $2$; then
$f \equiv 0$ and $F = \emptyset$ works. $|A| = 1$ cannot occur for a proper
$f$ with $f(V) = 0$.

## Background

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md):
  the analysis compares the forest with a feasible dual solution, whose value is at most the LP
  optimum; only this weak half of LP duality is used.

- [Weighted vertex cover by the pricing method](../weighted-vertex-cover-by-the-pricing-method/README.md):
  the simplest primal–dual approximation algorithm, a factor-2 analysis of the same shape.

## Sources

- M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest problems", *SIAM J. Comput.* 24(2) (1995), 296–317 (journal version), Theorem 2.4 and p. 297.
