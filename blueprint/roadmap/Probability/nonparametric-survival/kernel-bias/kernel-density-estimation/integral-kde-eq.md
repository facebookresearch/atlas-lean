# Expectation of the kernel density estimator

Let $f : \mathbb{R} \to \mathbb{R}$ be measurable with $0 \le f \le B$, and let $X_1, \dots, X_n$ be random variables on a probability space $(\Omega, P)$, each with law $f(x)\,dx$ (absolutely continuous with density $f$). Assume $n \ge 1$. For a kernel $K : \mathbb{R} \to \mathbb{R}$, a bandwidth $h$ and a sample $x_1, \dots, x_n$, write $\hat f_h(t) = \frac{1}{nh} \sum_{i=1}^{n} K\big(\frac{t - x_i}{h}\big)$ for the kernel density estimator at $t$. If $K$ is measurable and integrable and $h > 0$, then for every $t \in \mathbb{R}$

$$\mathbb{E}\big[\hat f_h(t)\big] = \int_{\mathbb{R}} K(u)\, f(t - hu)\,du,$$

where $\hat f_h(t)$ is computed from $X_1, \dots, X_n$. The $X_i$ need not be independent, and neither $K \ge 0$ nor $\int K = 1$ is assumed.
