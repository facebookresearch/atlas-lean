# Power-sum formula for weighted diagonal sums of trinomial coefficients

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. Let
$z, w \in \mathbb{C}$ and let $r_1, r_2, r_3 \in \mathbb{C}$ satisfy $r_1 + r_2 + r_3 = 2w$,
$r_1 r_2 + r_1 r_3 + r_2 r_3 = 2w^2$ and $r_1 r_2 r_3 = z + w^3$, that is, let $r_1, r_2, r_3$
be the zeros, with multiplicity, of $t^3 - 2wt^2 + 2w^2 t - (z + w^3)$. Then for every integer
$n > 0$

$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} w^{2n-3k} z^k =
(w^2 - w r_1 + r_1^2)^n + (w^2 - w r_2 + r_2^2)^n + (w^2 - w r_3 + r_3^2)^n.$$

The zeros (Cardano's $\alpha_{z,w}, \beta_{z,w}, \bar\beta_{z,w}$ in the paper) are given by
Vieta's relations.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 36 (`jis-2025-25.3.5-cor-36`).
