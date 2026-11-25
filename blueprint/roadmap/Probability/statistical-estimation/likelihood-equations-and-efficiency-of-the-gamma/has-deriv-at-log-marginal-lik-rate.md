# The rate score is the derivative in the rate

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. For $a, b > 0$ and positive size factors $s_i > 0$, the
[log marginal likelihood](log-marginal-lik.md) $\ell(a, b)$ is differentiable in the rate at $b$,
with derivative the [rate score](rate-score.md)
$S_b(a, b) = \sum_i \bigl(a/b - (a + k_i)/(b + s_i)\bigr)$:

$$\frac{\partial \ell}{\partial b}(a, b) = S_b(a, b).$$
