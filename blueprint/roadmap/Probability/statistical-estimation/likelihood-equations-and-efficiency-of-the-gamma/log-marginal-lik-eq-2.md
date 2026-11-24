# Closed form of the log marginal likelihood

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For $a, b > 0$ and positive size factors $s_i > 0$, the
[log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$ is

$$
\ell(a, b) = \sum_{i \in \iota} \Bigl(\sum_{j < k_i} \log(a + j) + k_i \log s_i - \log k_i! +
a \log b - (a + k_i) \log(b + s_i)\Bigr).
$$
