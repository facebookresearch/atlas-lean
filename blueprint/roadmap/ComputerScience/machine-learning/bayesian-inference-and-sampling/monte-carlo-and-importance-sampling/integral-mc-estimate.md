# The Monte Carlo estimator is unbiased

Let $\mu$ be a measure on $\Omega$, let $\nu$ be a
measure on $\alpha$, and let $f : \alpha \to \mathbb{R}$ be measurable and integrable with respect
to $\nu$. If $X_0, X_1, \ldots : \Omega \to \alpha$ are measurable and the pushforward of $\mu$
along each $X_i$ is $\nu$, then for every $n \ne 0$ the integral with respect to $\mu$ of the
Monte Carlo estimate $\frac{1}{n} \sum_{i < n} f(X_i)$ equals $\int f \, d\nu$.
