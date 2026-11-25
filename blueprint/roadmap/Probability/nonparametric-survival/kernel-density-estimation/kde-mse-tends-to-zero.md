# Mean-squared-error consistency of the kernel density estimator

Let $f : \mathbb{R} \to \mathbb{R}$ be measurable with $0 \le f \le B$, continuous at $t$, and let $X_0, X_1, \dots$ be independent random variables on a probability space $(\Omega, P)$, each with law $f(x)\,dx$. Let $K : \mathbb{R} \to \mathbb{R}$ be measurable and integrable with $\int K(u)\,du = 1$ and $\int K(u)^2\,du < \infty$, and let $h_N > 0$ be bandwidths with $h_N \to 0$ and $(N+1) h_N \to \infty$. Let

$$\hat f_N(t) = \frac{1}{(N+1) h_N} \sum_{i=0}^{N} K\Big(\frac{t - X_i}{h_N}\Big)$$

be the kernel density estimator built from the first $N + 1$ observations. Then

$$\mathbb{E}\big[(\hat f_N(t) - f(t))^2\big] \longrightarrow 0 \qquad \text{as } N \to \infty.$$

The kernel need not be bounded.
