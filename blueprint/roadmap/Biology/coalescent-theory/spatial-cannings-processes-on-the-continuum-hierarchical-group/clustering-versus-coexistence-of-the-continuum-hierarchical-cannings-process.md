# Clustering versus coexistence of the continuum hierarchical Cannings process

Let $\widehat X^\infty$ be the continuum hierarchical Cannings process on $\Omega_N^\infty \times \mathbb{K}$ with Haar measure $\mathfrak{h}$, started from a translation-invariant ergodic state with type marginal $\theta \in \mathcal{P}(\mathbb{K})$, under the conditions of the source.

1. **Convergence to equilibrium.** The limit $\nu_\theta = \lim_{t\to\infty} \mathcal{L}[\widehat X^\infty_t]$ exists in $\mathcal{P}\bigl(\widetilde{\mathcal{M}}(\Omega_N^\infty \times \mathbb{K})\bigr)$. Under $\nu_\theta$ the spatial projection is $\mathfrak{h}$ almost surely and the mean type projection is $\theta$.
2. **Dichotomy of equilibria.** Call $\nu_\theta$ **globally mono-type** (clustering) if

$$\nu_\theta = \int_{\mathbb{K}} \theta(da)\, \delta_{\mathfrak{h} \otimes \delta_a},$$

and **globally multi-type** (coexistence) otherwise; in the latter case $\nu_\theta = \delta_{\mathfrak{h} \otimes \theta}$.
3. **Coincidence of all dichotomies.** $\nu_\theta$ is globally multi-type if and only if $\widehat X^\infty$ is locally multi-type, if and only if $\widehat X^\infty$ is deterministic. Hence clustering occurs exactly in the stochastic, locally mono-type regime.

## Depends on

- [Stochastic versus deterministic dichotomy of the continuum hierarchical Cannings process](stochastic-versus-deterministic-dichotomy-of-the-continuum-hierarchical-cannings-process.md)

## Expansion

By duality, the probability that two individuals sampled far apart carry the same type at a large time equals the probability that their dual lineages have coalesced. If two typical dual lineages coalesce with positive probability then, as $t \to \infty$, they coalesce almost surely, so every finite region becomes mono-type and the equilibrium mixes over single types. If they never coalesce, the type composition stays $\theta$ everywhere. For stable migration the regimes split into one deterministic universality class and three stochastic ones (Fleming–Viot dominated, block-resampling dominated, and the balanced case).

## Sources

- A. Greven and F. den Hollander, *Continuum hierarchical Cannings process: I. Construction, duality and dichotomy*, arXiv:2611.12641 (2026), Section 1.5 (main theorems). <https://doi.org/10.48550/arXiv.2611.12641>
