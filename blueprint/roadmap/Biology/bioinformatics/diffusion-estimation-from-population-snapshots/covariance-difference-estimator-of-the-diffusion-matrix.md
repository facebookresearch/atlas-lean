# Covariance-difference estimator of the diffusion matrix

**Model.** Individuals (for example cells in expression space) follow the Itô SDE $d\mathbf{X} = \mathbf{v}(\mathbf{X},t)\,dt + \sigma(\mathbf{X},t)\,d\mathbf{B}$ with diffusion matrix $\mathbf{D} = \tfrac12\sigma\sigma^\top$, so the population density solves the Fokker-Planck equation

$$\partial_t p = -\sum_i \partial_{x_i}(v_ip) + \sum_{i,j}\partial_{x_i}\partial_{x_j}(D_{ij}p).$$

Only unpaired snapshots are observed: $n$ iid samples of $\mathbf{X}(t)$ and $n$ iid samples of $\mathbf{X}(t+\Delta t)$, so individual trajectories, and hence quadratic variation, are unavailable.

**Estimator.** Over a short step, $\operatorname{cov}\mathbf{X}(t+\Delta t) \approx \operatorname{cov}\bigl(\mathbf{X}(t) + \Delta t\,\mathbf{v}(\mathbf{X}(t),t)\bigr) + 2\mathbf{D}\Delta t$. With a regression estimate $\hat{\mathbf{v}}$ of the drift and unbiased sample covariances,

$$\widehat{\mathbf{D}} = \frac{1}{2\Delta t}\Bigl(\widehat{\operatorname{cov}}\bigl(\mathbf{X}(t+\Delta t)\bigr) - \widehat{\operatorname{cov}}\bigl(\mathbf{X}(t) + \Delta t\,\hat{\mathbf{v}}(\mathbf{X}(t),t)\bigr)\Bigr).$$

**Theorem (consistency).** Suppose $\mathbf{v}$, $\mathbf{D}$, their derivatives up to second order in $\mathbf{x}$ and first order in $t$, and $\mathbf{X}(t)$ have bounded fourth moments. Then for $n \ge 2$

$$\bigl\|\widehat{\mathbf{D}} - \mathbb{E}[\mathbf{D}(\mathbf{X}(t),t)]\bigr\|_\infty \le O\bigl(\|\hat{\mathbf{v}} - \mathbf{v}\|_\infty + \Delta t\bigr) + O_p\Bigl(\frac{1}{\Delta t\sqrt n}\Bigr).$$

So $\widehat{\mathbf{D}}$ consistently estimates the population-averaged diffusion when $\Delta t \to 0$, $\Delta t\sqrt n \to \infty$ and the drift estimate is consistent. A finite-sample version holds with explicit constants and probability $1 - \delta$.

## Expansion

Itô's formula for the second moments gives $\frac{d}{dt}\operatorname{cov}\mathbf{X} = \operatorname{cov}(\mathbf{X},\mathbf{v}) + \operatorname{cov}(\mathbf{v},\mathbf{X}) + 2\mathbb{E}\mathbf{D}$, and pushing samples forward by the drift accounts for the first two terms to $O(\Delta t^2)$. What remains is the spread no deterministic flow can produce, which is the diffusion. The error has a bias term from drift misspecification and time discretization and a variance term that blows up as $1/\Delta t$ because a small covariance difference is divided by $\Delta t$; the optimal step balances them. Without a drift estimate, transport and diffusion are confounded, which is why snapshot-only SDE inference is generally non-identifiable.

## Sources

- A. Forrow, "Consistent diffusion matrix estimation from population time series" (2024), Fokker-Planck model, covariance-difference estimator (Section 2), Theorem 1 and Theorem 2, <https://doi.org/10.48550/arXiv.2408.14408>.
