# Importance sampling with unit weight is plain Monte Carlo

For every $f : \alpha \to \mathbb{R}$, samples $X_0, X_1, \ldots : \Omega \to \alpha$, $n \in \mathbb{N}$ and $\omega \in \Omega$, the importance-sampling estimate with the constant weight $w = 1$ equals the Monte Carlo estimate:

$$\frac{1}{n}\sum_{i<n} 1 \cdot f(X_i(\omega)) = \frac{1}{n}\sum_{i<n} f(X_i(\omega)) .$$
