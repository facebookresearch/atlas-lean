# Bias–variance decomposition of the kernel density estimator

Let $f : \mathbb{R} \to \mathbb{R}$ be measurable and nonnegative, and let $X_1, \dots, X_n$ be random variables on a probability space $(\Omega, P)$, each with law $f(x)\,dx$. For a kernel $K : \mathbb{R} \to \mathbb{R}$, a bandwidth $h$ and a sample $x_1, \dots, x_n$, write $\hat f_h(t) = \frac{1}{nh} \sum_{i=1}^{n} K\big(\frac{t - x_i}{h}\big)$ for the kernel density estimator at $t$. If $K$ is measurable and bounded, then for every $n \in \mathbb{N}$, $h \in \mathbb{R}$ and $t \in \mathbb{R}$

$$\mathbb{E}\big[(\hat f_h(t) - f(t))^2\big] = \big(\mathbb{E}[\hat f_h(t)] - f(t)\big)^2 + \operatorname{Var}\big(\hat f_h(t)\big),$$

with the conventions $0^{-1} = 0$ and $y/0 = 0$ in $\hat f_h$. Independence of the $X_i$ is not needed.
