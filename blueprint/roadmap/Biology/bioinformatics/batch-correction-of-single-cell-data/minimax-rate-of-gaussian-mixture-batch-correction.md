# Minimax rate of Gaussian-mixture batch correction

**Model.** Cells are observed in batches $b=1,\dots,B$; cell $i$ of batch $b$ has an unobserved cluster label $a^*_{bi}\in[K]$ and a preprocessed expression vector (for example PCA scores) $X_{bi}\in\mathbb{R}^d$ with
$$X_{bi}\sim\mathcal{N}\bigl(\mu_k^*+\beta_{bk}^*,\ \Sigma_k^*\bigr)\quad\text{if }a^*_{bi}=k,$$
independently, where $\mu_k^*,\Sigma_k^*$ are cluster means and covariances and $\beta^*_{bk}$ is the batch effect on cluster $k$ in batch $b$, identified by $\sum_bn_{bk}\beta^*_{bk}=0$. Equivalently, a random batch effect $\beta_{bk}\sim\mathcal{N}(\beta^*_{bk},\Sigma^*_{0,k})$ plus cell noise. Batch correction estimates labels $a$ and shifts $\beta$ and outputs $\tilde X_{bi}=X_{bi}-\beta_{b a_{bi}}$; its loss relative to the oracle correction is
$$h(a,\beta,a^*,\beta^*)=\frac1n\sum_{b,i}\bigl\|\beta_{b a_{bi}}-\beta^*_{b a^*_{bi}}\bigr\|^2 .$$
Let $\mathrm{SNR}$ be the separation signal-to-noise ratio of the anisotropic mixture (the minimal pairwise separation of batch-shifted cluster distributions in the appropriate Mahalanobis-type sense). If $\omega=\min_{b,k\ne k'}\|\mu^*_k+\beta^*_{bk}-\mu^*_{k'}-\beta^*_{bk'}\|^2$ satisfies $\omega\ge2d\lambda_{\max}\log(\lambda_{\max}/\lambda_{\min})$, then $\frac13\frac{\lambda_{\min}}{\lambda_{\max}}\sqrt{\omega/\lambda_{\max}}\le\mathrm{SNR}\le2\sqrt{\omega/\lambda_{\min}}$, with $\lambda_{\max},\lambda_{\min}$ the extreme eigenvalues of the $\Sigma_k^*$.

**Theorem (lower bound).** With $B,K,d$ and the covariance conditioning bounded and $\mathrm{SNR}\to\infty$, for every $\alpha\in(0,\frac12)$,
$$\inf_{(a,\beta)}\sup_{(a^*,\beta^*)}\mathbb{E}\,h\ \ge\ \exp\Bigl(-(1+o(1))\frac{\mathrm{SNR}^2}{8}\Bigr)+\exp\bigl(-(1+o(1))\log n\bigr)$$
over a parameter class with balanced cluster sizes; if $\mathrm{SNR}=O(1)$ the minimax risk stays bounded away from $0$.

**Theorem (MoDaH achieves the rate).** The mixture-model data harmonization algorithm (an EM-type iteration alternating cluster assignment under anisotropic Gaussian likelihoods and re-estimation of $\mu,\beta,\Sigma$), initialized with $o(n)$ misclustered cells with probability $1-\eta$, satisfies for every iterate $t\ge\log n+1$
$$h(a^{(t)},\beta^{(t)},a^*,\beta^*)\le\max\{\Gamma,1\}\exp\Bigl(-(1+o(1))\frac{\mathrm{SNR}^2}{8}\Bigr)+\exp\bigl(-(1+o(1))\log n\bigr)$$
with probability at least $1-\eta-7n^{-1}-e^{-\mathrm{SNR}}$, matching the lower bound when $\log\Gamma=o(\omega)$; meanwhile its misclustering count is at most $\Omega\,n\exp(-(1+o(1))\mathrm{SNR}^2/8)$.

## Expansion

The loss has two sources: misassigned cells, which receive the wrong cluster's shift and contribute an $O(1)$ error each, occurring at the optimal clustering rate $\exp(-\mathrm{SNR}^2/8)$ for anisotropic Gaussian mixtures; and parametric error in estimating each $\beta^*_{bk}$ from $\Theta(n)$ cells, which is of order $1/n=\exp(-\log n)$. The lower bound combines a two-point testing argument for labels with a parametric bound for the shifts. The upper bound follows the iterative analysis of anisotropic clustering: once the initial misclustering is $o(n)$, each iteration contracts the error until it reaches the optimal exponent after about $\log n$ steps.

## Sources

- Y. Cao, Z. Ma, "MoDaH achieves rate optimal batch correction", arXiv:2512.09259 (2025), Section 2 (model, batch correction as inference, loss function and minimax rate), Proposition 1, Theorems 1–2, Proposition 2, <https://doi.org/10.48550/arXiv.2512.09259>.
