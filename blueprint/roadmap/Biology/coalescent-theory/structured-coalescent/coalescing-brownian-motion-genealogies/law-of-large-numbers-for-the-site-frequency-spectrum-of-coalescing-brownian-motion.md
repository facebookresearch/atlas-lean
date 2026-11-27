# Law of large numbers for the site frequency spectrum of coalescing Brownian motion

**Model.** For a range expansion in the plane, the angular positions of the ancestral lineages of a sample are modelled by coalescing Brownian motion. Let $E = \mathbb R$ (linear case) or $E = \mathbb S^1$ (circular case). Start $n$ particles at $1/n, 2/n, \dots, n/n$ (linear) or at $e^{2\pi ik/n}$, $k = 1,\dots,n$ (circular); they move as independent standard Brownian motions (on the circle, $e^{2\pi iW}$) until two meet, at which point they merge and continue as one. The trajectories form a genealogical tree of the $n$ sampled individuals. For $1 \le m \le n-1$ let $L_{n,m}$ be the total length of the branches of this tree that support exactly $m$ leaves; under infinite-sites mutation at rate $\theta$ per unit length, conditional on the tree the number of mutations carried by exactly $m$ sampled individuals (the site frequency spectrum) is Poisson with mean $\theta L_{n,m}$.

**Proposition (interior branch).** In the linear case, for $2 \le i \le n-m$, the expected length of the branch supporting the $m$ consecutive leaves starting at leaf $i$ is exactly $1/n^2$. The two edge branches ($i = 1$ and $i = n-m+1$) have infinite mean, so $\mathbb E[L_{n,m}] = \infty$ in the linear case.

**Theorem (weak law of large numbers).** In both the linear and circular cases, for every fixed $m \ge 1$,

$$nL_{n,m} \longrightarrow 1 \quad\text{in probability as } n \to \infty.$$

Thus the typical spatial site frequency spectrum is asymptotically **flat**: for each fixed $m$, the conditional mean $\theta L_{n,m}$ of the number of mutations in class $m$ satisfies $n\,\theta L_{n,m} \to \theta$ in probability, in contrast to the $\theta/m$ decay of the expected spectrum under Kingman's coalescent. The convergence is in probability only; it says nothing about the unconditional mean, which is infinite in the linear case.

## Expansion

In one dimension a block of leaves can only be ancestral to a contiguous set of sample positions, so a branch supporting $m$ leaves corresponds to a run of $m$ consecutive particles that have coalesced among themselves before either outer neighbour joins them. Its length is the time between the internal coalescence of the run and its merger with a neighbour, which is controlled by exit times of planar Brownian motion from cones (tail exponent $\pi/(2\theta_{\rm cone})$) and by the identity $\mathbb E[T_a \wedge T_{-b}] = ab$ for one-dimensional Brownian motion. Brownian scaling by the spacing $1/n$ gives expected length $1/n^2$ per interior run, and there are about $n$ interior runs, so the interior part of $L_{n,m}$ has mean $(n-m-1)/n^2 \sim 1/n$. Concentration of the interior part follows by coupling runs far apart with independent copies (contributions from distant runs decorrelate) and by showing that the runs within $n^{1/3+\epsilon}$ of the ends, including the two edge branches of infinite mean, contribute $o(1/n)$ in probability; the circular case is coupled to the linear one.

## Sources

- Yubo Shuai, "The site frequency spectrum for coalescing Brownian motion", *Stochastic Processes and their Applications* 180 (2025), 104521, <https://doi.org/10.1016/j.spa.2024.104521>. Numbering as in the preprint arXiv:2308.07533v1, <https://arxiv.org/abs/2308.07533v1>: Proposition 1.1 and Theorem 1.1 (Section 1), Lemmas 2.2–2.4 (Section 2) and Section 4.
