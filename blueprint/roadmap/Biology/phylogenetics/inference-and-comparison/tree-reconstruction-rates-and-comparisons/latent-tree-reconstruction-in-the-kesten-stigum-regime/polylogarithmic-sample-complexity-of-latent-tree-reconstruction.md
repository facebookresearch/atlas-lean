# Latent tree models are learnable from polylogarithmically many samples below the Kesten–Stigum bound

**Trees.** A *balanced tree* is a rooted complete binary tree with $h$ levels and $n = 2^h$ labeled leaves, with positive edge weights $w_e$.

**Models.**

- *GTR model.* For a rate matrix $Q$ on $q \ge 2$ states, reversible with respect to $\pi > 0$ and normalized so that its second eigenvalue is $\lambda_2 = -1$, the root state is drawn from $\pi$ and each child's state is drawn from row $\sigma_{\text{parent}}$ of $M^e = e^{w_eQ}$. This includes the CFN ($q = 2$) and Jukes–Cantor ($q = 4$) models.
- *Gaussian Markov random field on a tree (GMRFT).* A centered Gaussian vector $(\sigma_v)_{v\in V}$ with unit variances and covariances $\Sigma_{uv} = \prod_{e\in\mathrm{path}(u,v)}e^{-w_e}$, so the precision matrix is supported on the edges.

In both, $k$ i.i.d. samples of the leaf vector $\sigma_{[n]}$ are observed, and the task is to recover the tree topology (and edge weights).

**Theorem.** Let $0 < f < g < +\infty$ and consider balanced trees with $f < w_e < g$ for all edges. Let $g^\ast = \ln\sqrt2$ (the Kesten–Stigum threshold for binary trees, $2e^{-2w} = 1$).

1. (GMRFT, achievability.) If $g < g^\ast$, the topology can be recovered with high probability from $k = \kappa\log^2 n$ samples for a large enough $\kappa = \kappa(f,g)$, and all edge weights are estimated within constant tolerance.
2. (GTR, achievability.) If $g < g^\ast$, the same holds for all $q$-state GTR models with unknown rate matrix, with $k = \kappa\log^2 n$, $\kappa = \kappa(q,f,g)$.
3. (GMRFT, lower bound.) If $g > g^\ast$, the problem cannot in general be solved with fewer than $k = n^{\gamma}$ samples for some $\gamma = \gamma(f,g) > 0$.
4. (Gaussian root reconstruction threshold.) For a GMRFT on the infinite binary tree with all weights equal to $w$, the root state can be estimated from the level-$h$ leaves with nonvanishing information as $h\to\infty$ if and only if $2e^{-2w} > 1$; if $2e^{-2w} < 1$, the mutual information between the root and level $h$ is $\big[2e^{-2w}\big]^h\,\frac{1 - 2e^{-2w} + o(1)}{2 - 2e^{-2w}}$.

## Depends on

- [General time-reversible (GTR) rate matrix](../../../time-reversible-nucleotide-substitution-models/gtr-rate.md)

## Expansion

Distance methods that use only leaf states need $\mathrm{poly}(n)$ samples because deep internal distances are estimated from correlations decaying like $e^{-\text{depth}}$. Instead, the algorithm works bottom-up: after reconstructing the subtrees below a level, it estimates the hidden state at each internal node by a recursive linear combination of its children's estimates (using the eigenvector of $Q$ for $-1$ to map discrete states to reals). Below the Kesten–Stigum bound this estimator has bounded variance and bias factor close to $1$ even with estimated, inexact edge weights, so internal distances are estimated as accurately as leaf distances, with an additive bias per node. Each level uses $O(\log n)$ samples for concentration with a union bound, and there are $\log_2 n$ levels to correct errors through, giving $O(\log^2 n)$. Above the threshold, information about deep nodes decays exponentially with depth, and a two-point argument gives the polynomial lower bound.

## Sources

- Elchanan Mossel, Sebastien Roch, Allan Sly, "Robust estimation of latent tree graphical models: inferring hidden states with inexact parameters", arXiv (2011). Section 1 (definitions of balanced trees, GTR and GMRFT models), Theorems 1–4, Propositions 1–4. <https://doi.org/10.48550/arXiv.1109.4668>. Published version: IEEE Transactions on Information Theory 59(7) (2013), 4357–4373, <https://doi.org/10.1109/tit.2013.2251927>; locators above refer to the arXiv version.
