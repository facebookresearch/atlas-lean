# Monte Carlo estimates of almost-everywhere equal integrands agree

Let $\mu$ be a measure on a measurable space $\Omega$, $\nu$ a measure on a measurable space $\alpha$, and $X_0, X_1, \ldots : \Omega \to \alpha$ measurable samples whose law (pushforward of $\mu$) is $\nu$ for every $i$. The Monte Carlo estimate of $f$ from the first $n$ samples is $\widehat{f}_n(\omega) = \frac{1}{n}\sum_{i<n} f(X_i(\omega))$ (which is $0$ for $n = 0$). If $f, g : \alpha \to \mathbb{R}$ agree $\nu$-almost everywhere, then for $\mu$-almost every $\omega$,

$$\widehat{f}_n(\omega) = \widehat{g}_n(\omega) \quad \text{for every } n \in \mathbb{N}.$$
