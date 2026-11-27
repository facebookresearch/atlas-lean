# James–Stein shrinkage towards the grand mean dominates the MLE

Let $N \ge 4$, $\sigma^2 > 0$ and $X \sim \mathcal N(\theta, \sigma^2 I_N)$. Then the [grand-mean James–Stein estimator](james-stein-grand-mean.md) has finite quadratic risk and

$$\mathbb E \sum_{i=1}^N (\hat\theta_i - \theta_i)^2 < N \sigma^2 \qquad \text{for every } \theta \in \mathbb R^N,$$

while the estimator $X$ has risk $N\sigma^2$ (see, for $\sigma^2 = 1$, [the quadratic risk of the usual estimator](integral-sum-sq-sub-pi-gaussian-real.md)). The statement asserts the integrability of the loss together with the inequality, so the inequality is not satisfied vacuously by an infinite risk. This is Efron (2021), Theorem 1, equations (3.4)–(3.5), stated with the hypotheses given there; Efron credits the theorem to James and Stein (1961).

The proof is the argument used for shrinkage towards $0$. First, for $\sigma^2 = 1$, [Stein's unbiased risk estimate](integral-sum-sq-add-sub-pi-gaussian-real.md) is applied to $g(x) = -(N - 3)(x - \bar x \mathbf 1)/S$, whose divergence is $-(N - 3)^2/S$, giving the risk $N - (N - 3)^2\, \mathbb E[1/S]$. Second, $\mathbb E[1/S] < \infty$: $S$ is at least $1/(N+1)$ times $\sum_j (x_j - x_N)^2$, and conditionally on $x_N$ the other $N - 1 \ge 3$ coordinates form a Gaussian vector, whose inverse squared distance to $x_N \mathbf 1$ has an expectation bounded independently of its mean. Third, the general $\sigma^2$ follows by scaling.

## Background

- [James–Stein dominance](integral-james-stein-risk-lt.md): the version that shrinks towards $0$, with $p \ge 3$.

## Sources

- B. Efron, "Empirical Bayes: Concepts and Methods", author's manuscript (2021), https://efron.ckirby.su.domains/papers/2021EB-concepts-methods.pdf.
