# Jacobi continued fraction expansion

Let $K$ be a ring, not necessarily commutative, let
$(a_n)_{n \ge 0}$, $(\alpha_n)_{n \ge 0}$ and $(\beta_n)_{n \ge 0}$ be sequences in $K$, let
$\mu_0 \in K$, and let $(F_i)_{i \ge 0}$ be a sequence of formal power series over $K$ in the
variable $x$. These data form a Jacobi continued fraction expansion of $a$ when
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and, for every $i \ge 0$,
$(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$. Informally, the power series $F_i$ are the
tails of the continued fraction

$$
\sum_{n} a_n x^n = \cfrac{\mu_0}{1 - \alpha_0 x - \cfrac{\beta_1 x^2}{1 - \alpha_1 x - \cdots}}.
$$

## Sources

- Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms," Journal of Integer Sequences 24 (2021), Article 21.10.2, Section 1 (Jacobi continued fractions and Heilermann's formula), <https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.pdf>.
