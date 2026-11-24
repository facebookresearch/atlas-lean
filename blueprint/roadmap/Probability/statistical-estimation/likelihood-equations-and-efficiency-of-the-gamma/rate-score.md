# Rate score

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For real $a$ and $b$, the rate score is

$$S_b(a, b) = \sum_{i \in \iota} \Bigl(\frac{a}{b} - \frac{a + k_i}{b + s_i}\Bigr),$$

with the convention $x / 0 = 0$. For $a, b > 0$ and positive size factors $s_i > 0$ it is the
[derivative in the rate](has-deriv-at-log-marginal-lik-rate.md) $\partial \ell / \partial b$ of the
[log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$.
