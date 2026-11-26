# Stochastic versus deterministic dichotomy of the continuum hierarchical Cannings process

Fix $N \ge 2$ and let $\Omega_N^\infty$ be the continuum hierarchical group of order $N$: the closure of the iterated refinements of the discrete hierarchical group $\Omega_N$, with ultrametric balls $B_k(x)$ at every level $k \in \mathbb{Z}$ and Haar measure $\mathfrak{h}$. Let $\mathbb{K}$ be a compact Polish type space. The **continuum hierarchical Cannings process** $\widehat X^\infty = (\widehat X^\infty_t)_{t\ge 0}$ takes values in locally finite measures on $\Omega_N^\infty \times \mathbb{K}$ and describes a neutral population of colonies, one at each site, evolving by

- migration with multi-level rates $(c_k)_{k \in \mathbb{Z}}$, $c_k \in (0,\infty)$;
- Cannings block-resampling with reshuffling in $k$-balls, with finite resampling measures $(\Lambda_k)_{k\in\mathbb{Z}}$ on $(0,1]$;
- single-site Fleming–Viot resampling at the effective rate $d^\ast = d + |\Lambda_{-\infty}| \ge 0$.

The initial state is stationary and ergodic under the group action, with type marginal $\theta \in \mathcal{P}(\mathbb{K})$. Call $\widehat X^\infty$ **deterministic** if for every $t>0$ the law of $\widehat X^\infty_t$ is a point mass, and **stochastic** otherwise; call it **locally mono-type** if for every $t>0$ and $\mathfrak{h}$-a.e. $x$ there is a ball $B_k(x)$ on which $\widehat X^\infty_t = \mathfrak{h}|_{B_k(x)} \otimes \delta_a$ for some type $a$, and **locally multi-type** otherwise.

Write $\lambda_k = \int_{(0,1]} \Lambda_k(dr)$. Under the basic, non-triviality and regularity conditions of the source:

1. **Coincidence.** $\widehat X^\infty$ is deterministic if and only if it is locally multi-type; equivalently, stochastic if and only if locally mono-type.
2. **Criterion with block-resampling.** Suppose $\lambda_k > 0$ for some $k$. If $\sup_{k\in\mathbb{Z}} \lambda_k / c_k < \infty$ (resampling does not dominate migration), then

$$\widehat X^\infty \text{ is stochastic} \iff \sum_{k \ge 0} \frac{1}{c_k} \sum_{\ell = 0}^{k} \lambda_\ell = \infty .$$

If $\sup_k \lambda_k/c_k = \infty$, then $\widehat X^\infty$ is stochastic.
3. **Criterion without block-resampling.** Suppose $\lambda_k = 0$ for all $k$. If $d^\ast > 0$, then $\widehat X^\infty$ is stochastic if and only if $\sum_{k \ge 0} 1/c_k = \infty$ and $\sum_{k < 0} 1/c_k < \infty$, i.e. the migration is point-recurrent. If $d^\ast = 0$, then $\widehat X^\infty$ is deterministic.

In particular, Harris-recurrent but not point-recurrent migration gives a deterministic mass flow without block-resampling, but a stochastic, locally mono-type evolution once block-resampling is strong enough.

## Depends on

- [Cannings model of a haploid population](../multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Coalescing random walks dual to the voter model on a finite graph](../structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The process is built as a limit of processes on the truncated groups $\Omega_N^L$ and identified through a duality with a system of migrating, single-site delayed-coalescing and block-coalescing Lévy processes on $\Omega_N^\infty$. Two typical dual lineages either never coalesce, in which case sampled individuals are asymptotically independent and a law of large numbers makes the state deterministic and multi-type, or coalesce with positive probability, which yields random mono-type clusters. The sum conditions are recurrence criteria for the difference of two effective Lévy processes, with block-coalescence acting as an extra coalescence mechanism at each hierarchical level.

## Sources

- A. Greven and F. den Hollander, *Continuum hierarchical Cannings process: I. Construction, duality and dichotomy*, arXiv:2611.12641 (2026), Section 1.5 (main theorems). <https://doi.org/10.48550/arXiv.2611.12641>
