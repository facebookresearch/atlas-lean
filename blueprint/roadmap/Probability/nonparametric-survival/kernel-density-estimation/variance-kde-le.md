# Variance bound for the kernel density estimator

Let $f : \mathbb{R} \to \mathbb{R}$ be measurable with $0 \le f \le B$, and let $X_1, \dots, X_n$ be random variables on a probability space $(\Omega, P)$, each with law $f(x)\,dx$ (absolutely continuous with density $f$). Assume $n \ge 1$ and that $X_1, \dots, X_n$ are independent. For a kernel $K : \mathbb{R} \to \mathbb{R}$, a bandwidth $h$ and a sample $x_1, \dots, x_n$, write $\hat f_h(t) = \frac{1}{nh} \sum_{i=1}^{n} K\big(\frac{t - x_i}{h}\big)$ for the kernel density estimator at $t$. If $K$ is measurable with $\int K(u)^2\,du < \infty$ and $h > 0$, then for every $t \in \mathbb{R}$

$$\operatorname{Var}\big(\hat f_h(t)\big) \le \frac{B \int_{\mathbb{R}} K(u)^2\,du}{nh},$$

where $\hat f_h(t)$ is computed from $X_1, \dots, X_n$.
