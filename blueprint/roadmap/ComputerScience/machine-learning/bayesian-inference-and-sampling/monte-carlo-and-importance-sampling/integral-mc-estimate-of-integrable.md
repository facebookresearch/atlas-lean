# Monte Carlo is unbiased for an integrable integrand

Let $\mu$ be a measure on a measurable space $\Omega$, $\nu$ a measure on a measurable space $\alpha$, and $X_0, X_1, \ldots : \Omega \to \alpha$ measurable samples whose law (pushforward of $\mu$) is $\nu$ for every $i$. The Monte Carlo estimate of $f$ from the first $n$ samples is $\widehat{f}_n(\omega) = \frac{1}{n}\sum_{i<n} f(X_i(\omega))$ (which is $0$ for $n = 0$). Let $f : \alpha \to \mathbb{R}$ be integrable with respect to $\nu$ (measurability of $f$ is not assumed). Then for every $n \ne 0$,

$$\int \widehat{f}_n \, d\mu = \int f \, d\nu .$$
