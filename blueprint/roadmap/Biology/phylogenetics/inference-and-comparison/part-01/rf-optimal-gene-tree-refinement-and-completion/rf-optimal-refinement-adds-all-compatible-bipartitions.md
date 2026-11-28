# RF-optimal refinement adds all compatible bipartitions

**Setting.** Let $T$ be an unrooted, singly-labelled tree on leaf set $S$, and $t$ an unrooted, singly-labelled, possibly non-binary tree (e.g. a gene tree with low-support edges collapsed) on $R\subseteq S$. $T|_R$ is the restriction of $T$ to $R$ with degree-2 nodes suppressed, and $C(\cdot)$ denotes the set of non-trivial bipartitions. For singly-labelled trees the Robinson–Foulds (RF) distance is $|C(t_1)\,\triangle\,C(t_2)|$. Let $C_0$ be the bipartitions of $T|_R$ [compatible](../../../splits-compatibility-ultrametrics-and-upgma/compatible.md) with $t$; then $C(t)\cup C_0$ is pairwise compatible and defines a unique tree $t'$.

**Theorem 1.** A binary refinement $B$ of $t$ minimizes $\mathrm{RF}(B,T|_R)$ among all binary refinements of $t$ if and only if $C_0\subseteq C(B)$, i.e. iff $B$ refines $t'$.

**Corollary 1 (RF-optimal tree refinement).** Adding all bipartitions of $T|_R$ compatible with $t$ and then refining arbitrarily to a binary tree solves the RF-optimal tree refinement problem; the optimum is unique iff $t'$ is binary.

## Depends on

- [Compatible splits](../../../splits-compatibility-ultrametrics-and-upgma/compatible.md)

## Expansion

Build any binary refinement one edge at a time. A new bipartition lying in $C_0$ is shared with $T|_R$ and lowers the RF distance by one; any other new bipartition is absent from $T|_R$ and raises it by one. So $\mathrm{RF}(B,T|_R)=\mathrm{RF}(t,T|_R)-|X|+|Y|$ with $X=C(B)\setminus C(t)$ in $C_0$ and $Y$ the rest. All binary refinements add the same number $|X|+|Y|$ of edges, hence the distance is minimized exactly when $|X|=|C_0|$.

## Sources

- S. Christensen, E. K. Molloy, P. Vachaspati, A. Yammanuru, T. Warnow, "Non-parametric correction of estimated gene trees using TRACTION", Algorithms for Molecular Biology 15:1 (2020), section "TRACTION algorithm", Step 1, Theorem 1 and Corollary 1, <https://doi.org/10.1186/s13015-019-0161-8>, PMCID: PMC6942343.
