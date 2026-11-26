# Leaf-addition proximity to tree-child, orchard and tree-based networks

**Setting.** A *network* is a binary directed phylogenetic network on a leaf set $X$: a rooted acyclic digraph with a root of out-degree one, tree vertices (in-degree 1, out-degree 2), reticulations (in-degree 2, out-degree 1) and leaves labelled bijectively by $X$. Let $r$ be its number of reticulations. *Adding a leaf* subdivides an arc $(a,b)$ by a new vertex $w$ and adds a new arc from $w$ to a new leaf. For a class $\mathcal C$ of networks, the *leaf-addition proximity* $L_{\mathcal C}(N)$ is the minimum number of leaf additions turning $N$ into a member of $\mathcal C$. Leaf additions never remove reticulations, so the measure is studied for $\mathcal C \in \{\mathcal{TC}, \mathcal{O}r, \mathcal{TB}\}$ (tree-child, orchard, tree-based), all of which are reachable by enough leaf additions.

**Theorem.**
1. $L_{\mathcal{TC}}(N)$ is computable in $O(|N|)$ time. If $r \le 1$ then $L_{\mathcal{TC}}(N) = 0$, and otherwise
$$L_{\mathcal{TC}}(N) \le \left\lfloor \tfrac{3}{2} r - \tfrac{1}{2} \right\rfloor ,$$
and this bound is attained.
2. $L_{\mathcal{O}r}(N) = 0$ if $N$ is a tree and otherwise $L_{\mathcal{O}r}(N) \le r - 1$, which is sharp. Deciding whether $L_{\mathcal{O}r}(N) \le k$ is NP-complete, so computing $L_{\mathcal{O}r}$ is NP-hard.
3. $L_{\mathcal{TB}}(N)$ is computable in $O(|N|)$ time, and for $r \ge 1$
$$L_{\mathcal{TB}}(N) \le \left\lfloor \tfrac{r-1}{2} \right\rfloor ,$$
which is tight.

## Expansion

A network is tree-child exactly when it has no *omnian* (an internal vertex all of whose children are reticulations); a single new leaf hung below an omnian repairs it, and the linear-time algorithm counts the omnians that must be repaired after accounting for leaves that serve several of them. For orchard networks, adding a leaf to a tree arc preserves membership in both directions, so only reticulation arcs matter; the NP-hardness reduction encodes a satisfiability-type instance into the choice of which reticulation arcs receive new leaves. For tree-based networks, the characterisation "tree-based iff the arc set admits a cherry cover" turns the measure into a covering deficiency of the zig-zag decomposition, which is computed greedily. The extremal bounds follow from charging each new leaf to reticulations and constructing networks (chains of stacked reticulations) that need every charged leaf.

## Sources

- L. van Iersel, M. Jones, E. Julien, Y. Long, "Proximity Measures for Classes of Phylogenetic Networks", arXiv:2607.11325 (2026), Definition 3.1, Theorems 5.1, 5.2, 5.5, 5.7, 5.8 and 7.7, <https://doi.org/10.48550/arXiv.2607.11325>.
