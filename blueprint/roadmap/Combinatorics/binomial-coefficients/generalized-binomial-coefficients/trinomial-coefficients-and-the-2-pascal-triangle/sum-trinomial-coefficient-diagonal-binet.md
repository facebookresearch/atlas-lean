# Binet-type formula for diagonal sums of trinomial coefficients

Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. Let $z, w \in \mathbb{C}$
and let $r_1, r_2, r_3 \in \mathbb{C}$ be pairwise distinct with $r_1 + r_2 + r_3 = 2w$,
$r_1 r_2 + r_1 r_3 + r_2 r_3 = 2w^2$ and $r_1 r_2 r_3 = z + w^3$, that is, let $r_1, r_2, r_3$
be the three distinct zeros of $t^3 - 2wt^2 + 2w^2 t - (z + w^3)$. Then for every
$n \in \mathbb{N}$

$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 w^{2n-3k} z^k =
\sum_{i=1}^{3} \frac{(w^2 - w r_i + r_i^2)^{n+1}}{\prod_{j \ne i} (r_i - r_j)}.$$

The paper names the zeros $\alpha_{z,w}, \beta_{z,w}, \bar\beta_{z,w}$ by Cardano's formulas; the
right side is symmetric, so they are given here by Vieta's relations.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 28 (`jis-2025-25.3.5-thm-28`).
