# Central limit theorem for the composition of trade-off functions

For a symmetric trade-off function $f$ with $f(0) = 1$ define the functionals

$$
\mathrm{kl}(f) = -\int_0^1 \log|f'(x)|\,dx, \qquad \kappa_2(f) = \int_0^1 \log^2|f'(x)|\,dx, \qquad \kappa_3(f) = \int_0^1 \big|\log|f'(x)|\big|^3\,dx .
$$

Let $\{f_{n,i} : 1 \le i \le n\}$ be a triangular array of symmetric trade-off functions such that, as $n \to \infty$, $\sum_i \mathrm{kl}(f_{n,i}) \to K$, $\max_i \mathrm{kl}(f_{n,i}) \to 0$, $\sum_i \kappa_2(f_{n,i}) \to s^2$ and $\sum_i \kappa_3(f_{n,i}) \to 0$, with $K \ge 0$ and $s > 0$. Then

$$
f_{n,1} \otimes f_{n,2} \otimes \cdots \otimes f_{n,n} \to G_{2K/s}
$$

uniformly on $[0,1]$. The moment conditions exclude trade-off functions with $f(0) < 1$, so they do not say that every privacy guarantee becomes Gaussian under composition. For approximate differential privacy with parameters $(\varepsilon_{n,i}, \delta_{n,i})$ such that $\sum_i \varepsilon_{n,i}^2 \to \mu^2$, $\max_i \varepsilon_{n,i} \to 0$, $\sum_i \delta_{n,i} \to \delta$ and $\max_i \delta_{n,i} \to 0$, the composition converges to $G_\mu \otimes f_{0, 1 - e^{-\delta}}$, which keeps a non-Gaussian $\delta$ component when $\delta > 0$; it is Gaussian differential privacy exactly when the total $\delta$ vanishes, for example identical $(\varepsilon_n, \delta_n)$ with $\varepsilon_n\sqrt n \to \mu$ and $n\delta_n \to 0$. A finite-$n$ Berry–Esseen version holds for symmetric $f_1, \dots, f_n$ with $\kappa_3(f_i) < \infty$: with $\mu = 2\lVert \mathrm{kl} \rVert_1/\sqrt{\lVert \kappa_2 \rVert_1 - \lVert \mathrm{kl} \rVert_2^2}$ and $\gamma = 0.56\,\lVert \bar\kappa_3 \rVert_1/(\lVert \kappa_2 \rVert_1 - \lVert \mathrm{kl} \rVert_2^2)^{3/2}$, where $\bar\kappa_3(f) = \int_0^1 \big|\log|f'(x)| + \mathrm{kl}(f)\big|^3 dx$ and the norms are of the vectors of functionals, if $\gamma < 1/2$ then $G_\mu(\alpha + \gamma) - \gamma \le f_1 \otimes \cdots \otimes f_n(\alpha) \le G_\mu(\alpha - \gamma) + \gamma$ for $\alpha \in [\gamma, 1 - \gamma]$. The error is governed by this moment ratio $\gamma$; an $O(n^{-1/2})$ rate holds only when $\gamma$ is of that order, as for identical functions with fixed moments.

## Proof sketch

Represent $f_{n,i}$ by a pair of distributions and consider the log-likelihood ratio $L_{n,i}$; the functionals are its mean and moments under the null, with $\mathrm{kl}$ the Kullback–Leibler divergence. The trade-off function of the product is determined by the distribution of $\sum_i L_{n,i}$ under the null and the alternative, which by the Lyapunov central limit theorem (third-moment condition $\sum \kappa_3 \to 0$) becomes Gaussian with means $\mp K$ and variance $s^2$; a Gaussian location pair with these parameters has trade-off function $G_{2K/s}$. A Berry–Esseen bound for the sum of log-likelihood ratios gives the finite-$n$ version with error $\gamma$. For approximate privacy, $f_{\varepsilon,\delta} = f_{\varepsilon,0} \otimes f_{0,\delta}$ separates the $\varepsilon$ parts, which obey the theorem, from the $\delta$ parts, which multiply the graph by $1 - \delta_{n,i}$ each.

## Depends on

- [Tensor product of trade-off functions](tensor-product-of-trade-off-functions.md)

## Proof depends on

- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)
- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383v3, Theorems 3.4, 3.5 and 3.6 and Remark 1.
