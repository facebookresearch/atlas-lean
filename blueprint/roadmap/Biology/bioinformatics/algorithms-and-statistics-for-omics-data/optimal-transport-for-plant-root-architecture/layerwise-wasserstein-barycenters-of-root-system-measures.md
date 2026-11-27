# Layerwise-Wasserstein barycenters of root-system measures

**Setting.** A plant root system is encoded as a finite measure $\mu$ on $\mathbb R^d \times \mathbb R_{\ge 0}$, the last coordinate being depth. Let $\mu^V$ be its depth (vertical) marginal, $F_\mu(y) = \mu^V([0, y])/|\mu|$ its depth distribution function, and $\tilde\mu = |\mu|^{-1}(\mathrm{id} \times F_\mu)_\#\mu$ the vertically rescaled measure on $\mathbb R^d \times [0, 1]$, disintegrated as $\tilde\mu(dx, dl) = \tilde\mu_l(dx)\,dl$ into horizontal layers. The *layerwise-Wasserstein distance* is

$$d_{LW}^2(\mu, \nu) = W_2^2\Bigl(\frac{\mu^V}{|\mu^V|}, \frac{\nu^V}{|\nu^V|}\Bigr) + \int_0^1 W_2^2(\tilde\mu_l, \tilde\nu_l)\,dl,$$

and a layerwise-Wasserstein barycenter of a distribution $\Omega$ on such measures minimizes $\mu \mapsto \int d_{LW}^2(\mu, \nu)\,d\Omega(\nu)$ over probability measures.

**Theorem.**
1. *(Decomposition.)* $\mu$ is a layerwise-Wasserstein barycenter of $\Omega$ iff its vertical marginal is a Wasserstein barycenter of the vertical marginals and, for almost every level $l \in [0, 1]$, its layer $\tilde\mu_l$ is a Wasserstein barycenter of the layers $\tilde\nu_l$. For $\Omega$ concentrated on absolutely continuous measures the barycenter is unique.
2. *(Barycenters of roots are roots.)* Let $\mu_1, \dots, \mu_m$ be compactly supported *weak skeletal root measures* (probability measures, absolutely continuous with respect to one-dimensional Hausdorff measure, carried by finite unions of graphs of Lipschitz curves $y \mapsto g_i(y)$ branching downward from a single root point) such that $l \mapsto (\tilde\mu_i)_l$ is weak-$*$ continuous and each $F_{\mu_i}$ is bi-Lipschitz. Then every layerwise-Wasserstein barycenter with weights $\lambda_\alpha > 0$, $\sum_\alpha\lambda_\alpha = 1$, is again a weak skeletal root measure. In particular, layerwise-Wasserstein geodesics interpolate between root systems through root-like shapes, whereas ordinary $W_2$ interpolation does not.
3. *(Entropy.)* Shannon entropy splits as $S(\mu) = \int_0^1 S(\tilde\mu_l)\,dl + S(\mu^V)$ and is convex along layerwise-Wasserstein interpolation.

## Expansion

Ordinary optimal transport between two root systems moves mass horizontally and vertically at once and produces "clouds" rather than branching structures. Separating depth from horizontal position respects the oriented, gravity-aligned growth of roots: depth profiles are matched first by one-dimensional transport, then each depth layer is transported horizontally. Because each layer of a skeletal root is a finite set of points and one-dimensional quantile matching in depth is monotone, the barycenter's layers are again finitely many points moving Lipschitz-continuously in depth, i.e. a branching skeleton. This gives a metric for averaging and comparing root architectures across plants or genotypes.

## Sources

- Young-Heon Kim, Brendan Pass and David J. Schneider, "Optimal transport and barycenters for dendritic measures", Pure and Applied Analysis 2 (2020), 581–601, <https://doi.org/10.2140/paa.2020.2.581>; numbering as in arXiv:1910.08132: Proposition 2.5, Corollary 2.6, Theorem 3.6, Proposition 4.1 and Corollary 4.2.
