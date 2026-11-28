# Central limit theorem for punctuated equilibrium on Yule trees

**Setting (Yule–Ornstein–Uhlenbeck model with jumps).** A phylogeny grows as a pure-birth (Yule) process with birth rate $\lambda = 1$, stopped just before the $n$-th speciation event, so it has $n$ tips. Along each branch a continuous trait follows the Ornstein–Uhlenbeck process

$$dX(t) = -\alpha\,(X(t) - \theta)\,dt + \sigma_a\,dB_t, \qquad \alpha > 0,$$

and at a speciation the process splits into independent copies. Just after the $k$-th speciation event, independently on each daughter lineage, the trait jumps with probability $p_k$ by an independent $\mathcal{N}(0,\sigma_{c,k}^2)$ amount: $X(t^+) = X(t^-) + Z\zeta$ with $Z \sim \mathrm{Bernoulli}(p_k)$, $\zeta \sim \mathcal{N}(0,\sigma_{c,k}^2)$. Let $Y^{(n)}_r = (X^{(n)}_r - \theta)/\sqrt{\sigma_a^2/(2\alpha)}$ be the scaled tip traits and $\overline{Y}_n = \frac{1}{n}\sum_{r=1}^n Y^{(n)}_r$ their mean.

**Theorem (constant jump parameters).** Suppose $p_k \equiv p$ and $\sigma_{c,k}^2 \equiv \sigma_c^2 < \infty$.

1. If $\alpha > 1/2$ and $0 < p < 1$, the scaled conditional variance $\sigma_n^2 = n\operatorname{Var}(\overline{Y}_n \mid \mathcal{Y}_n)$ (conditional on the tree $\mathcal{Y}_n$) converges in probability to a random variable $\sigma_\infty^2$ with finite mean and variance, and $\sqrt{n}\,\overline{Y}_n$ converges weakly to a variance mixture of normals: for all $x \in \mathbb{R}$, $\lim_{n\to\infty}\varphi_{\sqrt{n}\,\overline{Y}_n}(x) = \mathcal{L}(\sigma_\infty^2)(x^2/2)$, where $\varphi$ is the characteristic function and $\mathcal{L}$ the Laplace transform.
2. If $\alpha = 1/2$, then $\sqrt{n/\ln n}\;\overline{Y}_n$ is asymptotically $\mathcal{N}(0,\ 2 + 4p\sigma_c^2/\sigma_a^2)$, and $n\ln^{-1}n\operatorname{Var}(\overline{Y}_n \mid \mathcal{Y}_n) \to 2 + 4p\sigma_c^2/\sigma_a^2$ in $L^2$.
3. If $0 < \alpha < 1/2$, then $n^{\alpha}\,\overline{Y}_n$ converges almost surely and in $L^2$ to a random variable with finite first two moments.

**Theorem (varying jump parameters, fast adaptation).** Suppose $(\sigma_{c,k}^4 p_k)_k$ is bounded. If $\alpha > 1/2$, $\sigma_{c,k}^4 p_k(1-p_k) \to 0$ with density $1$, and the two series of expected jump contributions along a random lineage and along the shared part of a random pair of lineages converge (to $\sigma_\Upsilon^2$ and $\sigma_\upsilon^2$), then $\sqrt{n}\,\overline{Y}_n$ is asymptotically normal with mean $0$ and variance

$$\frac{2\alpha+1}{2\alpha-1} + \frac{\sigma_\Upsilon^2 + \sigma_\upsilon^2}{\sigma_a^2/(2\alpha)}.$$

If $\alpha = 1/2$ and the analogous shared-lineage series normalized by $n\ln^{-1}n$ converges to $\sigma_\upsilon^2$, then $\sqrt{n/\ln n}\;\overline{Y}_n$ is asymptotically $\mathcal{N}(0,\ 2 + \sigma_\upsilon^2/\sigma_a^2)$.

So under fast adaptation ($\alpha > 1/2$) a Gaussian limit holds only when the randomness of whether jumps occur, measured by $\sigma_{c,k}^4p_k(1-p_k)$, disappears along the tree; with persistent jump randomness the limit is a non-degenerate normal mixture.

## Expansion

Conditionally on the tree, the tip traits are jointly Gaussian; their covariance is a sum over shared branches of OU decay factors $e^{-2\alpha(\cdot)}$, plus jump variances $\sigma_{c,k}^2 J_k$ at shared post-speciation points. The variance of the mean is therefore driven by the coalescence time $\tau^{(n)}$ of a random pair of tips and the number $\upsilon^{(n)}$ of shared speciation events. For $\alpha > 1/2$ the OU process forgets ancestry faster than the Yule tree adds tips, so the mean behaves like an average of almost independent terms and has $\sqrt{n}$ scaling; at $\alpha = 1/2$ a logarithmic correction appears; for $\alpha < 1/2$ the root dominates and the scaled mean converges to a non-trivial limit. The conditional-variance limit is constant exactly when the jump-indicator variance vanishes with density one, which is proved through variance bounds on sums of tree functionals (technical corollaries in Section 5).

## Sources

- Krzysztof Bartoszek, "A Central Limit Theorem for Punctuated Equilibrium", arXiv:1602.05189 (2016), Section 2 (model) and Theorems 4.2 and 4.7, <https://doi.org/10.48550/arXiv.1602.05189>. Published version: Stochastic Models 36:3, 473-517, 2020, <https://doi.org/10.1080/15326349.2020.1752242>.
