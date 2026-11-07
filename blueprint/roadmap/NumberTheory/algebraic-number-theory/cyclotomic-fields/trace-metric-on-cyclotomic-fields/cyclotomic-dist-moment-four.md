# Fourth moment of the trace distance on the cyclotomic box

Let $p$ be a prime, let $N$ be
a natural number, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of
unity, with fixed primitive $p$-th root of unity $\omega \in K$. Let $M_4(p, N)$ be the fourth
moment of the trace metric $d$ of $K$ over the box $B(p, N)$: the average of
$d(\alpha_a, \alpha_b)^4$ over all pairs $(a, b)$ of integer vectors in $\mathbb{Z}^{p-1}$ whose
coordinates lie in $[-N, N]$, where $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Then

$$
M_4(p, N) = \frac{2}{45} N (N + 1) (p - 1) \bigl( (2 N^2 + 2 N)
(5 p^5 - 8 p^4 + p^3 + 8 p^2 - 21 p - 18) - 3 (p^2 - p - 1)^2 \bigr).
$$

The asymptotic form $M_4(p, N) = \frac{4}{9} p^6 N^4 + O(p^5 N^4 + p^6 N^3)$ follows from this
exact formula.

## Sources

- Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10, Lemma 6 (`integers-2025-A10-lem-6`).
