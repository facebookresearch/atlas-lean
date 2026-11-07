# Upper bound for the measure of a Lüroth digit superlevel set

Let $m \in \mathbb{N}$, let
$F : \mathbb{R}^m \to \mathbb{R}$ be non-decreasing on $[2, \infty)^m$ for the coordinatewise
order, let $y \in \mathbb{R}$, and write $d_k(x)$ for the $k$-th Lüroth digit of $x$. Then the
Lebesgue measure of $\{x \in (0, 1] : F(d_1(x), \dots, d_m(x)) \ge y\}$ is at most

$$3^m \int_{\{x \in [2, \infty)^m : F(x) \ge y\}} \prod_{i=1}^{m} \frac{1}{x_i^2} \, dx.$$

The paper states this bound for $y = \Psi(n)$ under the hypotheses of its Theorem 4; only
the monotonicity of $F$ is used.

## Sources

- Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 6 (`integers-2024-A67-thm-6`).
