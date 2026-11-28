# Importance sampling with the Radon–Nikodym weight is consistent

Let $\mu$ be a measure on a measurable space $\Omega$ and let $\nu, \rho$ be σ-finite measures on a measurable space $\alpha$ with $\nu \ll \rho$. Let $X_0, X_1, \ldots : \Omega \to \alpha$ be measurable samples whose law under $\mu$ is $\rho$ for every $i$, and let $f : \alpha \to \mathbb{R}$ be integrable with respect to $\nu$. Use the Radon–Nikodym derivative $w = d\nu/d\rho$ as the importance weight, with estimate $\widehat{I}_n(\omega) = \frac{1}{n}\sum_{i<n} w(X_i(\omega))\, f(X_i(\omega))$ (an infinite weight counts as $0$). If moreover the samples are pairwise independent under $\mu$, then for $\mu$-almost every $\omega$,

$$\widehat{I}_n(\omega) \xrightarrow[n \to \infty]{} \int f \, d\nu .$$
