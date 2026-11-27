# Pareto property of the deep coalescence consensus problem

**Definitions.** For rooted binary trees $T$ (gene tree) and $S$ (species tree) on the same leaf set, the LCA mapping sends $v \in V(T)$ to $M_{T\rhd S}(v) = \mathrm{lca}_S(\mathrm{Le}(T_v))$, and for $X \subseteq Y$ let $\mathrm{pl}_S(X,Y)$ be the number of edges on the path from $\mathrm{lca}_S(Y)$ down to $\mathrm{lca}_S(X)$. The **deep coalescence cost** is

$$DC(T,S) = \sum_{\{u,v\}\in E(T),\,u<v}\mathrm{pl}_S\big(\mathrm{Le}(T_u),\mathrm{Le}(T_v)\big),$$

equivalent to the number of extra lineages. The **deep coalescence consensus tree problem** takes gene trees $T_1,\dots,T_n$ on a common leaf set $X$ and asks for species trees $S$ minimizing $\sum_i DC(T_i,S)$. The clusters of a tree are $\mathrm{Cl}(T) = \{\mathrm{Le}(T_v) : v\in V(T)\}$. A consensus problem is **Pareto on clusters** if for every instance and every optimal $S$, $\bigcap_i\mathrm{Cl}(T_i) \subseteq \mathrm{Cl}(S)$.

**Theorem.** The deep coalescence consensus tree problem is Pareto on clusters: every cluster present in all input gene trees is a cluster of every optimal species tree. Given a species tree lacking a consensus cluster, a tree containing it with no larger cost can be constructed in $O(nm + m^2)$ time for $m$ taxa.

## Depends on

- [Dc](../../../not-yet-classified/lcareconciliation/dc.md)
- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Suppose a cluster $X$ belongs to every gene tree but not to $S$. Restructure $S$ so that $X$ becomes a clade, by pulling the subtree induced by $X$ together and grafting the remaining taxa as in $S$ restricted to the complement. Partition the gene-tree edges into those inside $X$, those outside and the edge above $X$; a sequence of path-length inequalities shows each part costs no more in the new tree, and the cost strictly drops for the edges whose LCA images were separated by taxa outside $X$. Hence an optimal tree cannot omit $X$. Consequently all optimal species trees refine the strict consensus of the gene trees, so the search may be restricted to such refinements.

## Sources

- H. T. Lin, J. G. Burleigh, O. Eulenstein, "Consensus properties for the deep coalescence problem and their application for scalable tree search", BMC Bioinformatics 13(Suppl 10) (2012) S12, Definitions 1–7, Lemmas 1–5, Theorem 1 and Algorithm 1, <https://doi.org/10.1186/1471-2105-13-S10-S12>, PMCID PMC3382448.
