# Importance sampling is unbiased for an integrable integrand

Let $\mu$ be a measure on a measurable space $\Omega$, $\rho$ a measure on a measurable space $\alpha$ (the proposal), and $w : \alpha \to [0, \infty]$ a measurable weight with $w < \infty$ $\rho$-almost everywhere; let $\nu = w \cdot \rho$ be the target measure with density $w$ with respect to $\rho$. Let $X_0, X_1, \ldots : \Omega \to \alpha$ be measurable samples whose law under $\mu$ is $\rho$ for every $i$. The importance-sampling estimate of $f$ from the first $n$ samples is $\widehat{I}_n(\omega) = \frac{1}{n} \sum_{i<n} w(X_i(\omega))\, f(X_i(\omega))$, where an infinite weight counts as $0$ and the estimate is $0$ for $n = 0$. Let $f : \alpha \to \mathbb{R}$ be integrable with respect to $\nu$ (measurability of $f$ is not assumed). Then for every $n \ne 0$,

$$\int \widehat{I}_n \, d\mu = \int f \, d\nu .$$
