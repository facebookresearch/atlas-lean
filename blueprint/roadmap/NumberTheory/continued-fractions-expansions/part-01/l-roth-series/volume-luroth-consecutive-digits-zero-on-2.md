# Integral zero-one law for functions of consecutive Lüroth digits

Let $m \in \mathbb{N}$
and let $F : \mathbb{R}^m \to \mathbb{R}$ be a measurable function that is positive on
$[2, \infty)^m$ and non-decreasing there for the coordinatewise order. Let $M \in \mathbb{R}$
satisfy $F(x) \le M F(\lfloor x_1 \rfloor, \dots, \lfloor x_m \rfloor)$ for every
$x \in [2, \infty)^m$, and for $y \in \mathbb{R}$ put

$$G(y) = \int_{\{x \in [2, \infty)^m : F(x) \ge y\}} \prod_{i=1}^{m} \frac{1}{x_i^2} \, dx.$$

Let $(\Psi(n))_{n \ge 0}$ be a real sequence, write $d_k(x)$ for the $k$-th Lüroth digit of
$x$, and let $E$ be the set of $x \in (0, 1]$ such that
$F(d_{n+1}(x), \dots, d_{n+m}(x)) \ge \Psi(n)$ for infinitely many $n$. If
$\sum_{n \ge 0} G(\Psi(n)) < \infty$ then $E$ has Lebesgue measure $0$, and if
$\sum_{n \ge 0} G(M \Psi(n)) = \infty$ then $E$ has Lebesgue measure $1$.

Here $M$ is any constant with this property (the paper takes the supremum; a larger $M$ only
weakens the divergence condition). Unlike the paper, $\Psi$ need not be positive.

## Sources

- Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 4, with (6) and `G` from (7).
