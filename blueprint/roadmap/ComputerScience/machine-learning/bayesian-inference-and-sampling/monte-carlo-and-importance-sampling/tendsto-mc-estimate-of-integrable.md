# Monte Carlo is consistent for an integrable integrand

Let $\mu$ be a measure on a measurable space $\Omega$, $\nu$ a measure on a measurable space $\alpha$, and $X_0, X_1, \ldots : \Omega \to \alpha$ measurable samples whose law (pushforward of $\mu$) is $\nu$ for every $i$. The Monte Carlo estimate of $f$ from the first $n$ samples is $\widehat{f}_n(\omega) = \frac{1}{n}\sum_{i<n} f(X_i(\omega))$ (which is $0$ for $n = 0$). Assume moreover that the samples are pairwise independent under $\mu$, and let $f : \alpha \to \mathbb{R}$ be integrable with respect to $\nu$ (measurability of $f$ is not assumed). Then for $\mu$-almost every $\omega$,

$$\widehat{f}_n(\omega) \xrightarrow[n \to \infty]{} \int f \, d\nu .$$
