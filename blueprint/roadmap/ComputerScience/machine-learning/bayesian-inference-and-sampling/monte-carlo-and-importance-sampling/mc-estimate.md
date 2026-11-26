# Monte Carlo estimate

Given a function $f : \alpha \to \mathbb{R}$ and samples
$X_0, X_1, \ldots : \Omega \to \alpha$, the Monte Carlo estimate from the first $n$ samples at
$\omega \in \Omega$ is $\frac{1}{n} \sum_{i < n} f(X_i(\omega))$, which is $0$ when $n = 0$.
