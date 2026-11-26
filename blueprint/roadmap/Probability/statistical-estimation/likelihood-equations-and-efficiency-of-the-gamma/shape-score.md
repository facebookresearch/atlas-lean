# Shape score

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For real $a$ and $b$, the shape score is

$$S_a(a, b) = \sum_{i \in \iota} \Bigl(\psi_{k_i}(a) + \log b - \log(b + s_i)\Bigr),$$

with the [digamma increment](digamma-increment.md) $\psi_k(a) = \sum_{j < k} 1/(a + j)$ and the real
logarithm ($\log 0 = 0$, $\log x = \log |x|$ for $x < 0$). For $a, b > 0$ and positive size factors
$s_i > 0$ it is the [derivative in the shape](has-deriv-at-log-marginal-lik-shape.md)
$\partial \ell / \partial a$ of the [log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$.
