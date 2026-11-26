# Central limit theorem for the composition of trade-off functions

For a symmetric trade-off function $f$ with $f(0) = 1$ define the functionals

$$
\mathrm{kl}(f) = -\int_0^1 \log|f'(x)|\,dx, \qquad \kappa_2(f) = \int_0^1 \log^2|f'(x)|\,dx, \qquad \kappa_3(f) = \int_0^1 \big|\log|f'(x)|\big|^3\,dx .
$$

Let $\{f_{n,i} : 1 \le i \le n\}$ be a triangular array of symmetric trade-off functions such that, as $n \to \infty$, $\sum_i \mathrm{kl}(f_{n,i}) \to K$, $\max_i \mathrm{kl}(f_{n,i}) \to 0$, $\sum_i \kappa_2(f_{n,i}) \to s^2$ and $\sum_i \kappa_3(f_{n,i}) \to 0$, with $K \ge 0$ and $s > 0$. Then

$$
f_{n,1} \otimes f_{n,2} \otimes \cdots \otimes f_{n,n} \to G_{2K/s}
$$

uniformly on $[0,1]$. Consequently every hypothesis-testing-based privacy guarantee, in particular $(\varepsilon,\delta)$-DP with $\varepsilon_n\sqrt{n} \to \mu$ and $n\delta_n \to 0$, converges under many-fold composition to Gaussian differential privacy.

## Proof sketch

Represent $f_{n,i}$ by a pair of distributions and consider the log-likelihood ratio $L_{n,i}$; the functionals are its mean and moments under the null, with $\mathrm{kl}$ the Kullback–Leibler divergence. The trade-off function of the product is determined by the distribution of $\sum_i L_{n,i}$ under the null and the alternative, which by the Lyapunov central limit theorem (third-moment condition $\sum \kappa_3 \to 0$) becomes Gaussian with means $\mp K$ and variance $s^2$; a Gaussian location pair with these parameters has trade-off function $G_{2K/s}$. A Berry–Esseen version gives an explicit $O(n^{-1/2})$ approximation error.

## Depends on

- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)
- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)

## Proof depends on

- [Lossless adaptive composition of f-differential privacy](f-dp-adaptive-composition.md)
- [Approximate differential privacy as f-differential privacy](epsilon-delta-dp-as-f-dp.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
