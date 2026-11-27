# The shape score is the derivative in the shape

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For $a, b > 0$ and positive size factors $s_i > 0$, the
[log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$ is differentiable in the shape at $a$,
with derivative the [shape score](shape-score.md)
$S_a(a, b) = \sum_i \bigl(\psi_{k_i}(a) + \log b - \log(b + s_i)\bigr)$:

$$\frac{\partial \ell}{\partial a}(a, b) = S_a(a, b).$$
