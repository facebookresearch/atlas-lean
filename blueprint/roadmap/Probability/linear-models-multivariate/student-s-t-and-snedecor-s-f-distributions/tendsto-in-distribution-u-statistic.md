# Hoeffding's central limit theorem

Let $\mu$ be a probability measure on a measurable space $\mathcal{X}$, $m \in \mathbb{N}$ and $h : \mathcal{X}^m \to \mathbb{R}$ a symmetric kernel ($h(y \circ \sigma) = h(y)$ for every permutation $\sigma$) with $\mathbb{E}[h(X_1, \dots, X_m)^2] < \infty$ for i.i.d. $X_j \sim \mu$. For a sample $x \in \mathcal{X}^n$ let

$$U_n = \frac{1}{n(n-1)\cdots(n-m+1)} \sum_{\substack{(j_1, \dots, j_m) \\ \text{distinct}}} h(x_{j_1}, \dots, x_{j_m})$$

(the value is $0$ when $n < m$), let $\theta = \mathbb{E}\, h(X_1, \dots, X_m)$, $h_1(y) = \mathbb{E}\, h(y, X_2, \dots, X_m)$ and $\sigma_1^2 = \operatorname{Var}(h_1(X_1))$. Then, under the product laws $\mu^{\otimes n}$,

$$\sqrt n\, (U_n - \theta) \to N(0, m^2 \sigma_1^2) \quad \text{in distribution}.$$

## Sources

- W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math. Statist. 19 (1948), 293–325, §7.
