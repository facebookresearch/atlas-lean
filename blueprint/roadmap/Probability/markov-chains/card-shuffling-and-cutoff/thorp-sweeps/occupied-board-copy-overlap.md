# All-copy row–column overlap on an occupied board

There is $C>0$ such that the following holds. Take $\Omega\subseteq[m]\times[n]$, a Young diagram $\lambda$ with a bijection from $\Omega$ to its cells, and $1\le h\le mn$ such that every zero-indexed cell of $\lambda$ has row or column less than $h$. Let $V_\lambda$ be the complex Specht space, with its inherited Hilbert norm from the permutation basis of tabloids and action relabelled by the chosen bijection. Row and column groups consist of permutations preserving each respective occupied fiber. Take unitary irreducibles $\rho,\tau$ of these two groups on Euclidean dimensions $r,c$. For each restriction of $V_\lambda$, choose families of isometric equivariant inclusions $I_i$ and $J_j$ of the corresponding irreducible. Each family has pairwise orthogonal images and their sum contains the image of every intertwiner from that irreducible, so it includes all copies. Then

$$
\sum_{i,j}\|I_i^*J_j\|_{\rm op}^2\le
\exp\{C[(m+n+1)h^2\log(mn+2)+mn-|\Omega|]\}\min\{1,rc/\dim V_\lambda\}.
$$

**Conventions.** Use the complex tabloid Specht construction (linear span of translates of the column-alternating base tabloid), relabelled to the occupied board, and the two isotypic-copy conditions on actual intertwiners.

## Depends on

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)

## Proof outline

Quantitative row–column overlap estimates for the actual occupied-board action, with the missing cells and hook geometry controlled in the exponential term.

Construct a common Specht API and prove invariance under relabelling. Compare sums over all multiplicity copies, not merely a single pair of selected subspaces, and verify the operator norm rather than a Hilbert–Schmidt surrogate. The statement includes no full shuffle mixing consequence.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OccupiedOverlap.lean#L260-L262)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Row–column symmetry and contraction of coordinate sweeps](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf)
- [Pinned additional source formulation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OccupiedOverlap.lean#L263-L265)
