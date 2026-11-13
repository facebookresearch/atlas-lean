# The Monte Carlo estimator is consistent

**The Monte Carlo estimator is consistent** (strong law of large numbers). Let $\mu$ be a
measure on $\Omega$, let $\nu$ be a measure on $\alpha$, and let $f : \alpha \to \mathbb{R}$ be
measurable and integrable with respect to $\nu$. If $X_0, X_1, \ldots : \Omega \to \alpha$ are
measurable, pairwise independent under $\mu$, and the pushforward of $\mu$ along each $X_i$ is
$\nu$, then for $\mu$-almost every $\omega$ the Monte Carlo estimate
$\frac{1}{n} \sum_{i < n} f(X_i(\omega))$ converges to $\int f \, d\nu$ as $n \to \infty$.
