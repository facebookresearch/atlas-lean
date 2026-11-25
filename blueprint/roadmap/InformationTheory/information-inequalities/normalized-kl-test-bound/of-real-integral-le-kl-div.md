# Normalized KL test bound

Let $\mu$ and $\nu$ be probability measures on a measurable space $\alpha$, and let $f : \alpha \to \mathbb{R}$ be a measurable score such that $f$ is $\mu$-integrable, $e^{f}$ is $\nu$-integrable, and $f$ is normalized: $\int e^{f} \, d\nu = 1$. Then the Kullback–Leibler divergence in nats, a value in $[0, \infty]$, satisfies

$$\max\left\{\int f \, d\mu,\ 0\right\} \le D_{\mathrm{KL}}(\mu \parallel \nu).$$

No absolute continuity is assumed; if $\mu \not\ll \nu$ the divergence is $+\infty$.
