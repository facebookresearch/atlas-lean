# Zig-zag sampler for the coalescent posterior in τ-space

**τ-space.** An ultrametric binary tree on leaves $\{1,\dots,n\}$ is encoded as $(E_n,\mathbf{t}_n)$, where the ranked topology $E_n=(E_{n,1},\dots,E_{n,n-1})$ lists the pairs merged at successive coalescences and $\mathbf{t}_n\in(0,\infty)^{n-1}$ are the inter-coalescence times. Under Kingman's coalescent the tree has density

$$\pi(E_n,\mathbf{t}_n)=\exp\Big(-\sum_{i=1}^{n-1}\binom{n+1-i}{2}t_i\Big).$$

For fixed $E_n$ the times form the orthant $[0,\infty)^{n-1}$, and a boundary point with $t_i=0$ is of one of three types: (1) $i=1$, the first two leaves merge at time $0$ (a boundary of the whole space); (2) $E_{n,i-1}\notin E_{n,i}$, two simultaneous mergers, separating the orthants of two ranked topologies related by swapping the order of mergers $i-1$ and $i$; (3) $E_{n,i-1}\in E_{n,i}$, a triple merger, shared by the three orthants related by the two nearest-neighbour interchanges (pivots) of merger $i$ with its child merger. Gluing orthants along type 2 and 3 boundaries gives τ-space.

**Infinite-sites posterior.** Mutations fall on branches at rate $\theta/2$ with uniform locations, and the data $D_n$ are the leaves' mutation sets. With branch set $F_n$, branch lengths $l_\gamma$, mutation counts $m_\gamma$ and prior $\pi_0(\theta)$,

$$\pi(E_n,\mathbf{t}_n,\theta\mid D_n)\propto\prod_{\gamma\in F_n}\Big(\frac{\theta l_\gamma}{2}\Big)^{m_\gamma}\exp\Big(-\sum_{i=1}^{n-1}\frac{(n+1-i)(n+\theta-i)}{2}t_i\Big)\pi_0(\theta)$$

for $E_n$ compatible with $D_n$, and $0$ otherwise.

**Statement.** Run the hybrid zig-zag process with discrete states the compatible ranked topologies, continuous coordinates $(\mathbf{t}_n,\theta)\in(0,\infty)^n$, and boundary kernel that reflects (flips the hitting velocity) at type 1 boundaries and at $\theta=0$, crosses a type 2 boundary into the swapped topology, and at a type 3 boundary moves to one of the two other adjacent orthants (the two pivots) with probability $1/2$ each, flipping the hitting velocity in both cases; flip times are simulated by thinning with piecewise-constant upper bounds on the rates. If the initial law has a positive density on $\mathcal{F}\times(0,\infty)^n$, $\pi_0>0$, and $\partial_\theta\log\pi_0$ is bounded on compact subsets of $(0,\infty)$, then the infinite-sites posterior is stationary for this sampler.

## Depends on

- [Stationarity of zig-zag processes on hybrid discrete–continuous spaces](stationarity-of-zig-zag-processes-on-hybrid-spaces.md)
- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)
- [The infinite-sites sampling formula in the marked Kingman model](../measure-real-seg-sites-kingman-mutation.md)

## Expansion

The posterior is $C^1$ in $(\mathbf{t}_n,\theta)$ inside each orthant, so the flip rates are explicit; continuity of the posterior across type 2 and 3 boundaries (where the tree is the same degenerate tree seen from adjacent orthants) gives the skew-detailed balance needed by the hybrid-space stationarity theorem. On the data of Ward et al. ($n=55$) and on larger simulated data sets, the zig-zag sampler and a hybrid with Metropolis–Hastings moves mixed much better over trees than Metropolis–Hastings (effective sample sizes per second higher by one to three orders of magnitude), but explored the upper tail of the $\theta$-marginal less well, because high mutation rates require short trees. The same construction applies to the finite-sites Jukes–Cantor model.

## Sources

- J. Koskela, *Zig-zag sampling for discrete structures and non-reversible phylogenetic MCMC*, *Journal of Computational and Graphical Statistics* 31 (2022), 684–694, <https://doi.org/10.1080/10618600.2022.2032722>; preprint arXiv:2004.08807 (2020), <https://doi.org/10.48550/arXiv.2004.08807>. Preprint locators: Section 3 (the coalescent and τ-space, boundary types); Section 4 and Proposition 1 (infinite sites model); Section 5 (finite sites model).
