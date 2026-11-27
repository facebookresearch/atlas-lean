# Brownian coalescent point process limit of the Kingman comb under quenched conditional sampling

**Setting.** Consider the stationary standard Fleming–Viot population of constant size $1$, represented by the Bertoin–Le Gall flow of bridges $(\phi_{s,t})$ on $[0,1]$. The individuals at time $0$ are points of $[0,1]$, arranged in a linear order consistent with the genealogy. A *comb* is a function $C : [0,1] \to [0,\infty)$ with countable support. Its comb metric is $d_C(x,y) = \sup_{[x,y]} C$ for $x < y$, and the coalescence time of $x$ and $y$ is $d_C(x,y)$.

**Kingman comb.** There are i.i.d. uniform variables $(V_j)$ on $[0,1]$ and an independent sequence $T_j = \sum_{k \ge j+1} e_k$, with $e_k$ independent exponentials of rate $k(k-1)/2$, such that the coalescence time $\inf\{t > 0 : \phi_{-t,0}(x) = \phi_{-t,0}(y)\}$ equals $d_C(x,y)$ for all $x < y$ almost surely. Here $C = \sum_{j \ge 1} T_j \mathbf{1}_{\{V_j\}}$. The $T_j$ are the coalescence times of Kingman's coalescent, and $V_j$ marks where the corresponding split falls in the population.

**Brownian CPP.** For a $\sigma$-finite measure $\nu$ on $(0,\infty)$, the coalescent point process (CPP) with intensity $\nu$ is the random comb whose graph $\{(x,C(x)) : C(x) > 0\}$ is a Poisson point process with intensity $dx \otimes \nu(dy)$. The *Brownian CPP* $\mathcal{C}_\infty$ is the CPP with $\nu(dy) = 2y^{-2}dy$. It describes the rescaled genealogy of a critical birth–death process conditioned to survive to a large time. Write $S_a f(x) = a^{-1}f(a^{-1}x)$ for the space-and-depth rescaling and $k_t f = f\mathbf{1}_{[0,t)}$ for killing a comb at $t$.

**Theorem.**

1. *(Small-scale limit.)* $S_\varepsilon(C) \Rightarrow \mathcal{C}_\infty$ weakly in law as $\varepsilon \to 0$.
2. *(Size-biased family of a conditioned sample.)* Fix $n \ge 1$. Partition $[0,1]$ into the families of individuals with a common ancestor at time $-\varepsilon$; let $l^i_\varepsilon$ be their sizes and $B^i_\varepsilon$ the restricted combs. Sample $n$ i.i.d. uniform individuals conditioned to lie in one family, averaged over the population (quenched conditional sampling). The chosen family $(M_{n,\varepsilon}, l_{n,\varepsilon})$ then has law

$$ \mathbb{E} f(M_{n,\varepsilon}, l_{n,\varepsilon}) = \mathbb{E}\Bigl[\sum_i (l^i_\varepsilon)^n f(B^i_\varepsilon, l^i_\varepsilon) \Big/ \sum_i (l^i_\varepsilon)^n\Bigr]. $$

As $\varepsilon \to 0$,

$$ \bigl(S_\varepsilon(M_{n,\varepsilon}),\ \varepsilon^{-1} l_{n,\varepsilon}\bigr) \Rightarrow \bigl(k_{\mathcal{L}_n}(\mathcal{M}_\infty),\ \mathcal{L}_n\bigr), $$

where $\mathcal{M}_\infty$ is the CPP with intensity $\nu(dy)\mathbf{1}_{\{y < 1\}}$ and $\mathcal{L}_n$ is an independent Gamma variable with parameters $(n+1, 2)$.

## Depends on

- [Holding times of Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Expansion

Part 1 reduces to showing that, on $(t_0,\infty) \times I$ for bounded intervals $I$, the atoms of the rescaled comb converge to a Poisson process with intensity $2\, dx\, dt/t^2$. This is the small-depth behavior of Kingman's coalescence times, in which about $2/t$ lineages survive at depth $t$. Part 2 identifies the limit as an "$n$-size-biased" killed Brownian CPP. It is the genealogy of a critical birth–death family conditioned to survive a long time and biased by the $n$-th power of its size, which turns the exponential family size into a Gamma law with shape raised by $n$. The proof uses uniform integrability of $(2l^\varepsilon_1/\varepsilon)^n$ and an $L^2$ convergence to $n!$ (Proposition 4.3, Corollary 4.4).

Together these results couple the two standard genealogical models of a large exchangeable population: the Kingman coalescent (fixed total size, sparse samples) and the Brownian CPP (whole population, fixed foundation time).

## Sources

- Amaury Lambert and Emmanuel Schertzer, "Recovering the Brownian coalescent point process from the Kingman coalescent by conditional sampling", *Bernoulli* 25(1) (2019), 148–173. <https://doi.org/10.3150/17-BEJ971>
- Preprint version (the locators in this item follow its numbering): A. Lambert and E. Schertzer, "Recovering the Brownian Coalescent Point Process from the Kingman Coalescent by Conditional Sampling", arXiv:1611.01323 (2016), <https://doi.org/10.48550/arXiv.1611.01323>. Proposition 3.1 (Kingman comb), Proposition 3.4 (convergence to the Brownian CPP), Theorem 4.1 (conditional sampling and size-biased killed Brownian CPP), Proposition 4.3, Corollary 4.4.
