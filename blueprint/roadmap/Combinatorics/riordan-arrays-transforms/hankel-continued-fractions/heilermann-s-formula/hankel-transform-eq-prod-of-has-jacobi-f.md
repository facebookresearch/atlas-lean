# Heilermann's formula

Let $K$ be a commutative ring, let $a$, $\alpha$, $\beta$ be
sequences in $K$ and let $\mu_0 \in K$. Suppose that $a$ has Jacobi fraction data
$(\alpha, \beta, \mu_0)$: there are power series $F_0, F_1, \dots$ over $K$ with
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and $(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$ for
every $i \ge 0$. Then for every $n \ge 0$ the Hankel transform of $a$ at $n$, the determinant of
the $(n+1) \times (n+1)$ matrix $(a_{i+j})_{0 \le i, j \le n}$, equals

$$\mu_0^{n+1} \prod_{j=0}^{n-1} \beta_{j+1}^{\,n-j},$$

that is, $\mu_0^{n+1} \beta_1^n \beta_2^{n-1} \cdots \beta_n$, which is $\mu_0$ for $n = 0$.

## Sources

- Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms," Journal of Integer Sequences 24 (2021), Article 21.10.2, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex>, lines 110-117. Zero-indexed: `hankelTransform a n` is the determinant of the `(n + 1) x (n + 1)` Hankel matrix, and the product over `Finset.range n` with shift `beta (j + 1)` and exponent `n - j` gives `beta_1 ^ n, ..., beta_n ^ 1`; for `n = 0` the empty product yields `mu0`. Scope: only the determinant identity is stated; the Jacobi continued fraction data itself is carried by `HasJacobiFraction`.
