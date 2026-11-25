# Pairwise (tree) summation and reduction-order contracts

Let $x_1, \dots, x_n$ be floating-point numbers with $n \ge 1$, and let their sum be computed along a
binary computational tree of height $h$ whose leaves are the $x_j$ and whose internal nodes add their
two children. Assume every addition satisfies the standard model
$\mathrm{fl}(a + b) = (a + b)(1 + \delta)$ with $\lvert \delta \rvert \le u$, as IEEE arithmetic does for finite
inputs, a fixed rounding to nearest and no underflow or overflow. Then the computed sum $\hat s$ satisfies

$$\Bigl\lvert \hat s - \textstyle\sum_j x_j \Bigr\rvert \le \bigl((1 + u)^h - 1\bigr) \sum_j \lvert x_j \rvert
\le (1 + u)^h\, h\, u \sum_j \lvert x_j \rvert.$$

Indeed, $\hat s = \sum_j x_j \prod_{i \in \pi_j} (1 + \delta_i)$, where $\pi_j$ is the set of at most $h$ additions on the
path from $x_j$ to the root; expanding $\prod_{i \in \pi_j}(1 + \delta_i) - 1$ as a sum over nonempty subsets of $\pi_j$
bounds its absolute value by $(1 + u)^{\lvert \pi_j \rvert} - 1 \le (1 + u)^h - 1$. The second, weaker bound is the
form of Hallman and Ipsen's Theorem 2.4; the first is sharper (for $h = 2$ and $u = 1/10$ the coefficients are
$21/100$ and $121/500$).

Pairwise summation uses a balanced tree of height $\lceil \log_2 n \rceil$; sequential summation uses a tree of
height $n - 1$. Two parallel schedules realized by trees of height at most $h$ may return different values, but
both satisfy the bounds with that $h$; a fixed tree gives a deterministic result.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and
links it under the dependency sections, and states separately how underflow and overflow are excluded or
accounted for.

- Statement prerequisite: the standard model of floating-point addition with unit roundoff $u$.

## Sources

- E. Hallman and I. C. F. Ipsen, *Precision-aware deterministic and probabilistic error bounds for
  floating point summation*, Theorem 2.4 (deterministic bound in terms of the tree height), with the
  model (1.1) and the definition of computational trees in Section 2.
  <https://ipsen.math.ncsu.edu/ps/Summation.pdf>; also arXiv:2203.15928.
