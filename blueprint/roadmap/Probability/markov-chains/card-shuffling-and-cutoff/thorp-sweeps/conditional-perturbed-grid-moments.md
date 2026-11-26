# Conditional sweep moments on perturbed product grids

Take $b>0$ coordinates of lengths $m_j=2^{b_j}$. In stage $j$ permute each fiber along coordinate $j$, independently, with law $(1-z)U_j+zB_j$, where $U_j$ is uniform on its symmetric group and $B_j$ is the [binary coordinate-sweep law](binary-sweep-step-law.md) on its $b_j$-bit positions. Apply stages in order. Prescribe $h$ trajectories, disjoint at every stage boundary, changing only coordinate $j$ in stage $j$, and require at least one compatible choice of all fiber permutations. Conditional on these trajectories, compose on the left by the inverse of a fixed compatible sweep to obtain a permutation of the unmarked input sites, fixing all marked initial sites.

Let $S=\prod_jm_j$, $C(H)=\sum_{j,L}\log(m_j^{h_{jL}}/(m_j)_{h_{jL}})$, with $h_{jL}$ the number of marked trajectories through fiber $L$ at the start of stage $j$ and $(m)_r$ the falling factorial. Set $a=1/100$, $c(S)=a/100+1/\sqrt{\log S}$ and $e(S)=a/100-1/\sqrt{\log S}$. There exist integers $r,q\ge1$ and real $0<z_*\le1/2$ such that all grids with $r\le b_j\le2r$, all such prescribed feasible trajectories, every $z\in[0,z_*]$ and every unitary irreducible representation of the residual group of dimension $D$ satisfy

$$
\log\left(\operatorname{Re}\operatorname{tr}((Q^*Q)^q)\right)\le -c(S)\log D+e(S)h\log S-C(H),
$$

where $Q$ is the conditional mean representation matrix (the compatible weighted sum divided by the compatible-event probability), and the log of a zero moment is $-\infty$. The trace is real and is not divided by the representation dimension. The reference sweep in the source is chosen from feasibility; replacing it by another compatible sweep multiplies the residual operators by a group unitary and does not change the moment.

**Conventions.** Use the product grid, independent perturbed fiber laws, and feasible path event of the conditional model.

## Depends on

- [Conditional permutations on product grids](perturbed-grid-conditional-permutations.md)

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)

## Proof depends on

- [The explicit all-grid moment estimate](all-grid-quantitative-moment.md)

## Proof outline

Choose a sufficiently large scale by comparing the stated powers and logarithms. At this fixed scale the allowed widths up to the cutoff give finitely many grid shapes and finite choice events. For each nonempty event the uniform law gives positive weight and the conditional distance tends to zero as the perturbation tends to zero. Take a common positive perturbation cutoff, apply the linked estimate, and pass to the extended logarithm, including zero moments.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoordinateSweeps.lean#L306-L309)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Conditional coordinate sweeps and analytic transfer](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf)
