# Soft Robinson–Foulds distance and the cluster containment problem

Let $N$ be a rooted phylogenetic network on a taxon set $X$: a rooted acyclic digraph whose leaves are labelled bijectively by $X$, whose reticulation nodes have in-degree at least two, and whose other non-root nodes (tree nodes) have in-degree one. A tree is displayed by $N$ if it is obtained by deleting all but one incoming edge of each reticulation and suppressing degree-two nodes. The cluster of a tree node is the set of taxa below it; $B \subseteq X$ is a soft cluster of $N$ if $B$ is the cluster of a node in some tree displayed by $N$. Write $\mathcal C(N)$ and $\mathcal S(N)$ for the sets of clusters and soft clusters. For networks $N_1, N_2$ on $X$,

$$d_{\mathrm{RF}}(N_1, N_2) = \tfrac12\,\bigl|\mathcal C(N_1)\,\triangle\,\mathcal C(N_2)\bigr|, \qquad d_{\mathrm{SRF}}(N_1, N_2) = \tfrac12\,\bigl|\mathcal S(N_1)\,\triangle\,\mathcal S(N_2)\bigr|.$$

$d_{\mathrm{RF}}$ is computable in linear time, but deciding whether a given $B$ is a soft cluster of $N$ (the cluster containment problem) is NP-complete, so no polynomial-time algorithm for $d_{\mathrm{SRF}}$ is expected. It is solvable in linear time for reticulation-visible networks (each reticulation lies on every root-to-leaf path for some leaf), and for arbitrary networks by an exponential-time algorithm that repeatedly removes an exposed, non-trivial tree component: deciding whether $B$ is a soft cluster of $N$ reduces to the same question for $B$ or for a modified cluster $B'$ in a smaller network, according to how $B$ meets the leaves of that component.

## Expansion

Removing every reticulation splits $N$ into tree components, one rooted at the network root or at each reticulation; a component is exposed when all components immediately below it are trivial, and every network has an exposed non-trivial one. When that component is visible, Theorem 1 of the source gives the reduction directly; non-visible components need additional case analysis, and the resulting algorithm is exponential in the worst case but fast on empirical networks. $d_{\mathrm{SRF}}$ is then obtained by deciding containment in one network for the soft clusters of the other. Simulations in the source indicate that $d_{\mathrm{SRF}}$ over random networks is not normally distributed.

## Sources

- B. Lu, L. Zhang and H. W. Leong, "A program to compute the soft Robinson–Foulds distance between phylogenetic networks", BMC Genomics 18 (Suppl. 2) (2017) 111, <https://doi.org/10.1186/s12864-017-3500-5>, PMCID PMC5374702. Section "Concepts and notation", the decomposition of networks into tree components, and Theorem 1.
