# Identifiability of large phylogenies under nonparametric rate variation

Let $T = (V,E;[n],w)$ be a binary phylogeny with $n$ labelled leaves, internal vertices of degree $3$ and edge weights $w_e > 0$; let $d(u,v) = \sum_{e \in \mathrm{path}(u,v)} w_e$ be its tree metric and $\mathcal T[T]$ its topology. Under the $r$-state **Poisson model** (uniform stationary law on $r$ states, rate matrix $Q_{xy} = 1/r$ for $x \neq y$), each edge applies the channel $M(e) = \exp(w_e Q)$, with $M(e)_{xx} = \tfrac1r + (1-\tfrac1r)e^{-w_e}$. In the **rates-across-sites model** each site $i$ draws an i.i.d. scaling factor $\Lambda_i \ge 0$ from an unknown law and evolves on the scaled tree $\Lambda_i T$; normalize $\mathbb E[\Lambda] = 1$ and write $\phi(s) = \mathbb E[e^{-s\Lambda}]$ for its Laplace transform. Let $\overline{\mathcal D}[T,\Lambda,r]$ be the law of one site at the leaves.

Fix $0 < f \le g < \infty$ and $M > 0$, and assume:

1. (regular phylogeny) $f \le w_e \le g$ for every edge;
2. (bounded mass near $0$) $\phi^{-1}(e^{-6g}) \le M$, i.e. evolutionary distance $M$ under random scaling decorrelates at least as much as distance $6g$ without scaling.

**Theorem (identifiability).** There is $n_0 = n_0(f,g,M)$ such that, if $(T,\Lambda)$ and $(T',\Lambda')$ both satisfy the assumptions, both have at least $n_0$ leaves, and $\mathcal T[T] \neq \mathcal T[T']$, then

$$\overline{\mathcal D}[T,\Lambda,r] \neq \overline{\mathcal D}[T',\Lambda',r].$$

**Theorem (reconstruction).** Under the same assumptions, for every $0 < \delta < 1$ there is $\gamma > 0$ such that the topology can be reconstructed in polynomial time from $k = n^{\gamma}$ i.i.d. sites with probability at least $1 - \delta$.

So, although small trees can be non-identifiable when the rate distribution is unknown, large phylogenies are generically identifiable under a fully nonparametric rate distribution.

## Depends on

- [Site clustering statistic for rate variation](site-clustering-statistic-for-rate-variation.md)

## Expansion

The proof groups sites by rate before reconstructing the tree. A sparse set $\Upsilon$ of leaf pairs with edge-disjoint paths and lengths in $[2f, M]$ gives, for each site, an average of nearly independent agreement indicators; it concentrates at $U_\Upsilon(\Lambda_i) = |\Upsilon|^{-1}\sum_{(a,b)\in\Upsilon} e^{-\Lambda_i d(a,b)}$, a strictly decreasing function of the site rate. Sites are binned by this statistic; within a bin the rates are nearly equal, so the bin behaves like a Poisson model on a fixed rescaling of $T$, and distance-based reconstruction with distorted-metric arguments recovers the topology. The mass-near-$0$ condition guarantees that a constant fraction of sites have rates in a bounded window $[g/M, 2/(1-e^{-5g})]$, which is enough signal. Identifiability follows because the reconstruction succeeds with probability tending to $1$ from the leaf distribution alone.

## Sources

- Elchanan Mossel, Sebastien Roch, "Identifiability and inference of non-parametric rates-across-sites models on large-scale phylogenies", arXiv (2011). Section 2 (Definitions 1–5, Assumption 1, Theorems 1 and 2), Section 5 (Proposition 7). <https://doi.org/10.48550/arXiv.1108.0129>. Published version: Journal of Mathematical Biology 67(4) (2013), 767–797, <https://doi.org/10.1007/s00285-012-0571-4>; locators above refer to the arXiv version.
