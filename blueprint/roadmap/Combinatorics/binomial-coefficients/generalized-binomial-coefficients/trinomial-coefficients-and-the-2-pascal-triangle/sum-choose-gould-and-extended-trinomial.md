# Gould-type identities for binomial and extended trinomial coefficients

For complex $u$
and $j \in \mathbb{N}$ write $\binom{u}{j}$ for the generalized binomial coefficient and
$\binom{u}{j}_2$ for the coefficient of $t^j$ in
$(1 + t + t^2)^u = \sum_{i \ge 0} \binom{u}{i}(t + t^2)^i$ (Comtet's extension). Then for all
complex $x$, $y$ and every $n \in \mathbb{N}$,

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{x}{k}\binom{y - 3x}{n - 3k} =
\sum_{k=0}^{n} \binom{x}{k}\binom{y - 2k}{n - k}(-3)^k$$

and

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{-x}{n - 3k}_2 \binom{x}{k}(-1)^k = (-1)^n \binom{x}{n}.$$

The paper's Eq. (25) also equates the first two sums with
$\sum_k \binom{2x}{n-k}_2 \binom{y-2x}{k}(-1)^{n-k}$; that expression is left out because it is
false as printed: at $x = 2$, $y = 1/3$, $n = 1$ it equals $-23/3$, while both sides of the
first identity equal $-17/3$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 21 (`jis-2025-25.3.5-thm-21`).
