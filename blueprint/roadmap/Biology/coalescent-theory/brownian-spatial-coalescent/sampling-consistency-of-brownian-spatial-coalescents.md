# Sampling consistency of Brownian spatial coalescents

**Setting.** Brownian spatial coalescents on the $d$-dimensional torus $E$ with transition measures $\boldsymbol\nu = (\nu_{n,\vec k})$, as in the linked characterization. A spatial coalescent is *sampling consistent* if for every choice of initial locations $x_1, \dots, x_n$ there is a probability measure $\mu_{x_1,\dots,x_n}$ on $E$ such that the coalescent started from $x_1, \dots, x_n$ has the same law as the coalescent induced on the first $n$ lineages when an extra lineage starts at $x_{n+1} \sim \mu_{x_1,\dots,x_n}$. Let $\Delta = \{\boldsymbol\xi : \xi_1 \ge \xi_2 \ge \dots \ge 0,\ \sum_i \xi_i \le 1\}$ and let $(\lambda_{n,\vec k})$ be the merger rates of the non-spatial $\Xi$-coalescent for a finite measure $\Xi$ on $\Delta$.

**Theorem (characterization).** A label invariant Brownian spatial coalescent is sampling consistent if and only if there is a finite measure $\Xi$ on $\Delta$ with

$$\nu_{n,\vec k}(d\boldsymbol z) = \lambda_{n,\vec k}\, d\boldsymbol z, \qquad (n, \vec k) \in \mathcal{M},$$

that is, every transition measure is a constant multiple of Lebesgue measure on $E^m$. This is the *Brownian spatial $\Xi$-coalescent*.

**Proposition (sampling measures).** For $\Xi \ne 0$ the sampling measures are unique and given by

$$\mu^\Xi_{x_1,\dots,x_n}(dy) = \frac{N^\Xi(x_1, \dots, x_n, y)}{N^\Xi(x_1, \dots, x_n)}\, dy,$$

and there is a unique random probability measure $\mu^\Xi$ on $E$ with $\mathbb{E}[\mu^\Xi(dx_1) \cdots \mu^\Xi(dx_n)] = N^\Xi(x_1, \dots, x_n)\, dx_1 \cdots dx_n$ for all $n$. The law of $\mu^\Xi$ is the unique stationary distribution of the spatial $\Xi$-Fleming–Viot process with Brownian motion, and the genealogy of a sample from that process at stationarity is the Brownian spatial $\Xi$-coalescent.

**Theorem (drift of lineages).** If $\boldsymbol\nu(d\boldsymbol z) = \boldsymbol\lambda\, d\boldsymbol z$ and the coalescent starts from distinct points, then until just before the first merger (for $d = 1$, until the first meeting of any pair) the lineage positions $\boldsymbol Z_t \in E^n$ solve

$$d\boldsymbol Z_t = d\boldsymbol B_t + \nabla \log N^{\boldsymbol\nu}(\boldsymbol Z_t)\, dt$$

with $\boldsymbol B$ an $nd$-dimensional Brownian motion on the torus.

## Depends on

- [Brownian spatial coalescent and its transition measures](brownian-spatial-coalescent-and-transition-measures.md)
- [Merger rates of a coalescent with simultaneous multiple collisions](../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

Sampling consistency means an extra sampled individual carries no information about the others beyond its location, which forces space to be homogeneous in the merger mechanism: transition measures must be translation-invariant, hence Lebesgue multiples, and the remaining non-spatial consistency is exactly the $\Xi$-coalescent condition. Independent Brownian motions never meet in $d \ge 2$, so mergers must come from an attraction; the drift $\nabla \log N$ is a Doob $h$-transform with $h = N^{\boldsymbol\nu}$, pulling lineages together at the rate needed to produce mergers in any dimension.

## Sources

- P. Koepernik, "The Brownian Spatial Coalescent", arXiv:2401.08557 (2024), Definition 1.10, Theorem 1.11, Proposition 1.12, Theorem 1.14, Proposition 1.19 and Theorems 1.20 and 1.25, <https://doi.org/10.48550/arXiv.2401.08557>.
