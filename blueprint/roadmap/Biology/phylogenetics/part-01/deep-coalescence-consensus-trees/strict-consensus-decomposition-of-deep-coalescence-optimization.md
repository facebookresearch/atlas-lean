# Strict-consensus decomposition of deep coalescence optimization

**Definitions.** For gene trees $I = (T_1,\dots,T_n)$ on a common leaf set, the **strict consensus tree** $H$ is the (possibly non-binary) tree with $\mathrm{Cl}(H) = \bigcap_i\mathrm{Cl}(T_i)$. For a binary tree $T$ refining $H$ and an internal node $h$ of $H$ with children $c_1,\dots,c_m$, the **cut** $\mathrm{Cut}_{H,h}(T)$ is the minimal connected subtree of $T$ containing the LCA images of $c_1,\dots,c_m$, each of its leaves $x$ being relabelled by the leaf set below it; $\mathrm{Cut}_{H,h}(I)$ applies this to every gene tree.

**Theorem.** If $S$ is an optimal species tree for the deep coalescence consensus problem on $I$ and $h$ is an internal node of $H$, then $\mathrm{Cut}_{H,h}(S)$ is an optimal species tree for the instance $\mathrm{Cut}_{H,h}(I)$. Conversely, optimal solutions of the subproblems at all internal nodes of $H$ can be grafted together into an optimal solution of the full instance.

## Depends on

- [Pareto property of the deep coalescence consensus problem](pareto-property-of-the-deep-coalescence-consensus-problem.md)
- [Deep-coalescence cost](../../../not-yet-classified/lcareconciliation/dc.md)

## Expansion

By the Pareto property every optimal $S$ refines $H$, so the cut is defined. If $\mathrm{Cut}_{H,h}(S)$ were not optimal for the subinstance, replacing it inside $S$ by a better subtree $R'$ changes LCA images only for gene-tree edges lying between the consensus node $h$ and its consensus children; edges below the children or outside $h$ keep their costs, and the edges in between cost exactly their subinstance cost, so the total strictly decreases, a contradiction. Each consensus node therefore defines an independent problem on its number of children rather than on all taxa, and any heuristic (e.g. SPR local search) run on these small subproblems returns a tree that is guaranteed to satisfy the Pareto property, with large speed-ups when gene trees share many clades.

## Sources

- H. T. Lin, J. G. Burleigh, O. Eulenstein, "Consensus properties for the deep coalescence problem and their application for scalable tree search", BMC Bioinformatics 13(Suppl 10) (2012) S12, Definitions 12–13, Theorem 2 and the divide-and-conquer method, <https://doi.org/10.1186/1471-2105-13-S10-S12>, PMCID PMC3382448.
