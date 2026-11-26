# Brownian spatial coalescent and its transition measures

**Setting.** Let $E$ be the $d$-dimensional torus ($d \ge 1$) with heat kernel $p_t$, and let $\mathcal{P}$ be the finite sets of disjoint nonempty subsets of $\mathbb{N}$ (sets of lineages). For $\pi \in \mathcal{P}$ let $E^\pi_\circ$ be the set of location vectors $\boldsymbol x \colon \pi \to E$ in which no pair of lineages shares a location if $d \ge 2$, and at most one pair does if $d = 1$. A *spatial coalescent* is a Feller Markov process on $\mathcal{X} = \{(\pi, \boldsymbol x) : \pi \in \mathcal{P},\ \boldsymbol x \in E^\pi_\circ\}$ whose partition coordinate only changes by merging blocks; it is *label invariant* if relabelling the initial lineages relabels the process.

**Definition.** A spatial coalescent is a *Brownian spatial coalescent* if, conditional on the genealogical forest and on the times and locations of all coalescence events, the lineages follow independent Brownian bridges along the branches of the forest, and independent Brownian motions after the last coalescence event they take part in.

**Theorem (characterization).** Let $\mathcal{M}$ be the set of tuples $(n, \vec k) = (n, (k_1, \dots, k_m))$ with $n \ge 2$, $k_1 \ge \dots \ge k_m \ge 1$ and $\sum_i k_i \le n$.
1. Every label invariant Brownian spatial coalescent is uniquely characterized by a family of finite *transition measures* $\boldsymbol\nu = (\nu_{n,\vec k})_{(n,\vec k) \in \mathcal{M}}$, with $\nu_{n,\vec k}$ a finite measure on $E^m$.
2. For a given family $\boldsymbol\nu$, a Brownian spatial coalescent with transition measures $\boldsymbol\nu$ exists if and only if its normalization function $N^{\boldsymbol\nu} \colon \mathcal{X} \to [0, \infty]$ is finite and continuous.

For two lineages at $\boldsymbol x = (x_1, x_2)$, the time $\tau$ and location $\xi$ of their merger have law

$$P^{\boldsymbol x}(d\tau, d\xi) = \frac{1}{N^{\boldsymbol\nu}(\boldsymbol x)}\, p_\tau(x_1 - \xi)\, p_\tau(x_2 - \xi)\, e^{-\bar\nu_2 \tau}\, \nu_{2,2}(d\xi)\, d\tau, \qquad \bar\nu_2 = |\nu_{2,2}|,$$

so $N^{\boldsymbol\nu}(\boldsymbol x)$ is the total mass of the unnormalized right-hand side. In general $\bar\nu_n = \sum_{\vec k} \binom{n}{k_1 \cdots k_m} |\nu_{n,\vec k}|$, and the law of the decorated forest is the non-spatial one with rates replaced by transition measures and one heat-kernel factor per branch.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

The defining property is what any population whose individuals move as independent Brownian motions should satisfy backwards in time, whatever its branching mechanism: conditioning on the tree and on where and when branchings happened turns each branch into a Brownian bridge. Replacing $E$ by a single point recovers a non-spatial coalescent with rates $\lambda_{n,\vec k} = |\nu_{n,\vec k}|$, so transition measures are the spatial analogue of merger rates. The constraint is analytic: the normalizing integral over decorated forests must be finite and continuous in the starting configuration, which is what makes the Feller property hold.

## Sources

- P. Koepernik, "The Brownian Spatial Coalescent", arXiv:2401.08557 (2024), Definition 1.5, Theorems 1.7–1.8, Equation for the two-particle law (Section 1.3), and Theorem 2.12, <https://doi.org/10.48550/arXiv.2401.08557>.
