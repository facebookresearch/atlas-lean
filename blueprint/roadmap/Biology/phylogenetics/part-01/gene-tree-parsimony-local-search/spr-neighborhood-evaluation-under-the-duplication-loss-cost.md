# SPR neighborhood evaluation under the duplication–loss cost

**Setting.** Let $S$ be a rooted binary species tree on $n$ leaves and $\mathcal G$ a collection of $k$ rooted binary gene trees whose leaves are labeled by species of $S$. For $G \in \mathcal G$, the LCA mapping $\mathcal M_{G,S}(g) = \mathrm{lca}_S(\text{species below } g)$ defines the duplications $\mathrm{Dup}(G,S) = \{g : \mathcal M(g) \in \mathcal M(\mathrm{Ch}(g))\}$ and the losses $\mathrm{Loss}(G, S) = \sum_g \mathrm{Loss}(G,S,g)$, where $\mathrm{Loss}(G,S,g) = 0$ if $g$ and both children map to the same node and otherwise $\sum_{g' \in \mathrm{Ch}(g)} |d(\mathcal M(g), \mathcal M(g')) - 1|$ with $d$ the edge distance in $S$ restricted to the species of $G$. The duplication–loss cost is $\Delta(\mathcal G, S) = \sum_{G} (|\mathrm{Dup}(G,S)| + \mathrm{Loss}(G,S))$, and gene tree parsimony seeks $S$ minimizing it. Let $m = |\mathrm{Le}(S)| + |\mathrm{Le}(G)|$ (gene trees of similar size). For a non-root node $v$ of $S$, $\mathrm{SPR}_S(v)$ is the set of trees obtained by pruning the subtree rooted at $v$ and regrafting it on any other edge of the planted tree; $\mathrm{SPR}_S$ is the union over $v$.

**Theorem.**

1. (SPR-RS) The duplication–loss costs $\Delta(\mathcal G, T)$ of all $T \in \mathrm{SPR}_S(v)$ for a fixed pruned node $v$, and hence a minimizer, can be computed in $O(km)$ time.
2. (SPR-S) A tree of minimum cost in the whole SPR neighborhood $\mathrm{SPR}_S$ can be found in $O(kmn)$ time, a factor $n$ faster than recomputing each of the $\Theta(n^2)$ neighbors from scratch.
3. (TBR-S) A tree of minimum cost in the rooted TBR neighborhood can be found in $O(kmn^2)$ time.

The same bounds hold for the deep coalescence cost; for a uniquely labeled $G$ with $\mathrm{Le}(G) = \mathrm{Le}(S)$ it equals $\mathrm{Loss}(G,S) - 2|\mathrm{Dup}(G,S)|$.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Fix the pruned node $v$ and colour gene-tree nodes by how their LCA images relate to the subtree at $v$: for nodes whose images are unaffected the mapping and loss counts do not change under any regraft; for the others the new image is $\mathrm{lca}(v, \cdot)$ of a mapping into the pruned tree, and the change in losses as the regraft point moves along $S$ is piecewise constant with $\pm 1$ jumps at boundary nodes determined by a few LCA images. Accumulating these jumps by one traversal of $S$ gives all regraft costs for one gene tree in $O(m)$ time. A TBR move is an SPR move with a rerooted pruned subtree, which reduces TBR-S to $O(n^2)$ SPR-RS instances.

## Sources

- M. S. Bansal, J. G. Burleigh and O. Eulenstein, "Efficient genome-scale phylogenetic analysis under the duplication-loss and deep coalescence cost models", *BMC Bioinformatics* 11 (Suppl. 1) (2010) S42, Definitions 1–7, Problem 1, Lemmas 1–6, Theorems 1–2 and the section on the deep coalescence cost model. <https://doi.org/10.1186/1471-2105-11-s1-s42> (PMC3009515)
