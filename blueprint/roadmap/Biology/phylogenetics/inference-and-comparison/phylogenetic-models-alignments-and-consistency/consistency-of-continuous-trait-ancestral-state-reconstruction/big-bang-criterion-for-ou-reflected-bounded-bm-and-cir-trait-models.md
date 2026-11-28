# Big bang criterion for OU, reflected, bounded Brownian and CIR trait models

For a nested sequence of trees of bounded height, the [big bang condition](big-bang-condition-characterizes-consistent-ancestral-state-reconstruction.md) ($|\partial\mathbb{T}_n(s)|\to\infty$ for every $s>0$) is necessary and sufficient for the existence of a consistent estimator of the root trait value when the trait evolves along the branches by any of the following processes, with all parameters other than the root value known. In each case the regularity condition $(A_1)$, $\mathbb{E}\{\phi[Y(t)]\mid Y(0)\} = u(t)\phi[Y(0)] + v(t)$ and $\operatorname{Var}\{\phi[Y(t)]\mid Y(0)\}\le Ct$ on $[0,h^*]$, holds with the stated choices, and the support-overlap condition $(A_2)$ is immediate.

| Model | Dynamics | $\phi(y)$ | $u(t)$ | $v(t)$ | $C$ |
|---|---|---|---|---|---|
| Ornstein–Uhlenbeck | $dY = \alpha(\mu - Y)\,dt + \sigma\,dB$ | $y$ | $e^{-\alpha t}$ | $(1-e^{-\alpha t})\mu$ | $\sigma^2$ |
| Reflected BM on $[0,\infty)$ | $Y = \lvert X\rvert$, $X$ a BM with variance $\sigma^2$ per unit time | $y^2$ | $1$ | $\sigma^2 t$ | $4\sigma^2 Y(0)^2 + 2\sigma^4 h^*$ |
| Bounded BM on $[0,1]$ | BM with reflecting barriers at $0$ and $1$ | $\cos(\pi y)$ | $e^{-\sigma^2\pi^2 t/2}$ | $0$ | $\sigma^2\pi^2$ |
| Cox–Ingersoll–Ross | $dY = \alpha(\mu - Y)\,dt + \sigma\sqrt{Y}\,dB$ | $y$ | $e^{-\alpha t}$ | $\mu(1-e^{-\alpha t})$ | $(Y(0)+\mu/2)\sigma^2$ |

Consequently the explicit estimator $\hat\rho = \phi^{-1}\bigl(k^{-1}\sum_i [\phi(Y_{i,k}) - v(t_{i,k})]/u(t_{i,k})\bigr)$ over $k$ leaves whose ancestors split within distance $1/k$ of the root is consistent in each model; for the reflected BM it averages bias-corrected squared trait values and takes a square root.

## Depends on

- [Big bang condition characterizes consistent ancestral state reconstruction](big-bang-condition-characterizes-consistent-ancestral-state-reconstruction.md)

## Proof sketch

OU: $\operatorname{Var}[Y(t)\mid Y(0)] = \frac{\sigma^2}{2\alpha}(1-e^{-2\alpha t}) \le \sigma^2 t$. Reflected BM: $Y^2 = X^2$, so the Gaussian moments $\mathbb{E}[X(t)^2] = X(0)^2+\sigma^2t$ and $\mathbb{E}[X(t)^4] = X(0)^4 + 6\sigma^2tX(0)^2 + 3\sigma^4t^2$ give $\operatorname{Var}[Y(t)^2\mid Y(0)] = 4\sigma^2tY(0)^2 + 2\sigma^4t^2$; the mean itself is not affine in $Y(0)$, which is why $\phi(y)=y^2$ is used. Bounded BM: unfolding the method-of-images transition density turns $\mathbb{E}\cos(\pi X(t))$ into a Gaussian integral over $\mathbb{R}$, so $\cos(\pi y)$ is an eigenfunction: $\mathbb{E}[\cos\pi X(t)\mid X(0)] = e^{-\sigma^2\pi^2t/2}\cos\pi X(0)$, and the same identity for $\cos 2\pi y$ bounds the variance by $1-e^{-\sigma^2\pi^2 t}\le\sigma^2\pi^2t$. CIR: the standard conditional mean and variance give $\operatorname{Var}\le (Y(0)+\mu/2)\frac{\sigma^2}{\alpha}(1-e^{-\alpha t})\le (Y(0)+\mu/2)\sigma^2 t$.

## Sources

- Nhat L. Vu, Thanh P. Nguyen, Binh T. Nguyen, Vu Dinh and Lam Si Tung Ho, "When can we reconstruct the ancestral state? Beyond Brownian motion", *Journal of Mathematical Biology* 86 (2023), 88, <https://doi.org/10.1007/s00285-023-01922-8>. Preprint version: arXiv:2207.12897 (2022), Section 4, Theorems 4.1 (OU), 4.2 (reflected BM), 4.3 (bounded BM), 4.4 (CIR), <https://doi.org/10.48550/arXiv.2207.12897>.
