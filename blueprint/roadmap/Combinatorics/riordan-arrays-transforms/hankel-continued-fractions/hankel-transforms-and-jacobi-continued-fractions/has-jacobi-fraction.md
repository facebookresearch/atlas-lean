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

This records only the continued fraction identities, not Heilermann's formula for the Hankel
determinants of $a$.

## Sources

- Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms," JIS 24 (2021), Article 21.10.2, `https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117 (source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`; lines 110-117 SHA-256 `11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`). JIS concept: `jis_dep_heilermann_049f63eb`.
