# Monte Carlo with exact Beta posterior draws

Let $a, b > 0$ and $k \le n$ natural numbers, and let $B = \mathrm{Beta}(a + k,\, b + (n - k))$ be the Beta-Binomial posterior after $k$ successes in $n$ trials. Let $g : \mathbb{R} \to \mathbb{R}$ be measurable with $g \in L^2(B)$, and let $\theta_0, \theta_1, \ldots : \Omega \to \mathbb{R}$ be measurable, mutually independent under a measure $\mu$, each with law $B$. Then for every $m \ne 0$ the Monte Carlo average $\widehat{g}_m = \frac{1}{m}\sum_{i<m} g(\theta_i)$ satisfies

$$\int \widehat{g}_m \, d\mu = \int g \, dB \qquad\text{and}\qquad \operatorname{Var}_\mu(\widehat{g}_m) = \frac{\operatorname{Var}_B(g)}{m} .$$
