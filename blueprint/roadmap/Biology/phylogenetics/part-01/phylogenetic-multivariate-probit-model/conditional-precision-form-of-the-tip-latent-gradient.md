# Phylogenetic multivariate probit model and the conditional-precision form of its gradient

**Model.** $N$ taxa are related by a rooted tree $\mathcal{G}$, and each carries $P$ traits: $P_b$ binary and $P - P_b$ continuous. Every node $i$ has a latent vector $\mathbf{x}_i\in\mathbb{R}^P$ evolving by multivariate Brownian motion,

$$\mathbf{x}_i \sim \mathcal{N}\big(\mathbf{x}_{\mathrm{pa}(i)},\ t_i\,\boldsymbol{\Sigma}\big),$$

where $t_i$ is the length of the branch above $i$ and $\boldsymbol{\Sigma}$ is the across-trait covariance per unit time. Observed tip traits are $y_{ij} = \operatorname{sign}(x_{ij})$ for binary $j$ (threshold $0$) and $y_{ij} = x_{ij}$ for continuous $j$. With a conjugate normal prior $\mathcal{N}(\boldsymbol{\mu}_0, \kappa_0^{-1}\boldsymbol{\Sigma})$ at the root, the $N\times P$ tip matrix is matrix normal,

$$\mathbf{X}\sim\mathcal{MN}_{N\times P}\big(\mathbf{1}\boldsymbol{\mu}_0^\top,\ \boldsymbol{\Psi},\ \boldsymbol{\Sigma}\big),\qquad \boldsymbol{\Psi} = \mathbf{V}_{\mathcal{G}} + \kappa_0^{-1}\mathbf{1}\mathbf{1}^\top,$$

where $(\mathbf{V}_{\mathcal{G}})_{kl}$ is the shared root-to-tip path length of tips $k$ and $l$. The augmented likelihood is $p(\mathbf{Y},\mathbf{X}) = \mathbb{I}(\mathbf{Y}\mid\mathbf{X})\,p(\mathbf{X})$.

**Identifiability.** For a binary trait $j$, rescaling $x_{\cdot j}\mapsto kx_{\cdot j}$ together with the matching rescaling of $\Sigma_{jj}$ leaves the likelihood unchanged. Its marginal variance must therefore be fixed, while continuous-trait variances are free parameters. This rules out a Wishart prior on $\boldsymbol{\Sigma}^{-1}$. Instead write $\boldsymbol{\Sigma} = \mathbf{D}\mathbf{C}\mathbf{D}$, put an LKJ prior on the correlation matrix $\mathbf{C}$ (uniform when $\eta = 1$) and log-normal priors on the free standard deviations.

**Proposition.** Let $\boldsymbol{\Omega} = \boldsymbol{\Psi}\otimes\boldsymbol{\Sigma}$ be the joint covariance of $\operatorname{vec}(\mathbf{X}^\top)$. Then

$$\boldsymbol{\Omega}^{-1}\big(\operatorname{vec}(\mathbf{X}^\top) - \operatorname{vec}(\mathbf{M}^\top)\big) = \begin{pmatrix}\mathbf{P}_1(\mathbf{x}_1 - \mathbf{m}_1)\\ \vdots\\ \mathbf{P}_N(\mathbf{x}_N - \mathbf{m}_N)\end{pmatrix},$$

where $\mathbf{m}_i$ and $\mathbf{P}_i$ are the mean and precision of the conditional law $p(\mathbf{x}_i\mid\mathbf{x}_{-i})$ of tip $i$ given all other tips. All $(\mathbf{m}_i, \mathbf{P}_i)$ can be computed by one post-order and one pre-order traversal of the tree. The gradient of the truncated-normal log-density used by bouncy-particle or Hamiltonian samplers therefore costs $O(NP^2)$ even when the tree is random, instead of the $O(N^3)$ needed to invert $\boldsymbol{\Psi}$.

## Expansion

The identity is the coordinate form of the Gaussian conditional: with $\boldsymbol{\Lambda} = \boldsymbol{\Omega}^{-1}$ in $P\times P$ blocks, $\mathbf{P}_i = \boldsymbol{\Lambda}_{ii}$ and $\mathbf{m}_i = \boldsymbol{\mu}_0 - \boldsymbol{\Lambda}_{ii}^{-1}\sum_{k\ne i}\boldsymbol{\Lambda}_{ik}(\mathbf{x}_k - \boldsymbol{\mu}_0)$. Rearranging gives row $i$ of $\boldsymbol{\Lambda}(\mathbf{x} - \boldsymbol{\mu})$. On a tree, conditioning tip $i$ on all others amounts to Gaussian message passing. Post-order passes summarize each subtree and pre-order passes summarize its complement, both in $O(P^2)$ per node after a one-time $P^3$ factorization of $\boldsymbol{\Sigma}$. The model was applied to HIV immune-escape traits, estimating correlations between binary and continuous phenotypes while the tree is sampled jointly from sequence data.

## Proof depends on

- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md)

## Sources

- Z. Zhang, A. Nishimura, P. Bastide, X. Ji, R. P. Payne, P. Goulder, P. Lemey and M. A. Suchard, "Large-scale inference of correlation among mixed-type biological traits with phylogenetic multivariate probit models", arXiv:1912.09185 (2019), Section 2 (model, identifiability and the $\mathbf{D}\mathbf{C}\mathbf{D}$ decomposition) and Section 3 (Proposition 1 and the linear-order gradient), <https://doi.org/10.48550/arXiv.1912.09185>.
