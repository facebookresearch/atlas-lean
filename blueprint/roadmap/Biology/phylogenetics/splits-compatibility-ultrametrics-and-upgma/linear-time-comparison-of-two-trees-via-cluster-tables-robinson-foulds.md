# Linear-time Robinson–Foulds comparison of two trees (Day)

Let $T_1$ and $T_2$ be rooted trees on the same $n$ labelled leaves in which every internal vertex has at least two children (no vertex has exactly one child), so that each tree has at most $2n - 1$ vertices, and call the set of leaves below a vertex a clade. Without this convention, subdividing edges keeps $n$ fixed while the traversals grow, and the bounds below hold with the total number of vertices in place of $n$. Day (1985), as described by Briand, Dessimoz, El-Mabrouk and Nevers (2022, Algorithm Implementation and the paragraph introducing Day's data structure), renumbers the leaves in the order of a postorder traversal of $T_1$, so that every clade of $T_1$ is a contiguous run of leaf numbers summarized by its smallest and largest values, and stores the nontrivial clades of $T_1$, those of internal vertices (with at least two leaves; there are at most $n - 1$ of them), in a table with $n$ rows, each clade at the row of one of its two endpoints without collisions, so that membership of an interval is tested in constant time. Singleton clades are shared by both trees and are not stored. A postorder traversal of $T_2$ with the same numbering records, at each vertex, the minimum, the maximum and the number of leaves below it; the clade is contiguous exactly when the number of leaves equals maximum minus minimum plus one, and a table lookup then decides whether it is a clade of $T_1$. Each traversal does constant work per vertex, so the shared clades, and hence the Robinson–Foulds distance, are computed in time linear in the number of vertices, which is $O(n)$ under the degree convention. For unrooted trees, rooting both at the same arbitrarily chosen leaf turns their splits into clades, which reduces the unrooted case to the rooted one; this is the cluster form of the [Robinson–Foulds distance](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/rf-dist.md).

## Depends on

- [Robinson–Foulds distance](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/rf-dist.md)
- [Clusters seen from a leaf are edge sides](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/cluster-eq-edge-side.md)

## Expansion

1. Definitions: rooted trees on a common label set with every internal vertex having at least two children, the resulting bound $2n - 1$ on the number of vertices, clades, and the reduction of splits of unrooted trees to clades by rooting at a common leaf.
2. The postorder renumbering and the interval property of the clades of $T_1$.
3. The table with $n$ rows: storing each nontrivial clade interval of $T_1$ at the row of its left or right endpoint without collisions, and the constant-time membership test.
4. The traversal of $T_2$ and the size test, giving the shared clades and the distance in linear time.

## Sources

- S. Briand, C. Dessimoz, N. El-Mabrouk and Y. Nevers, A linear time solution to the labeled Robinson–Foulds distance problem, Syst. Biol. 71 (2022), 1391–1403, Notation and Concepts; Algorithm Implementation. <https://doi.org/10.1093/sysbio/syac028>
- Original result: W. H. E. Day, Optimal algorithms for comparing trees with labeled leaves, J. Classification 2 (1985), 7–28. <https://doi.org/10.1007/BF01908061> The algorithm follows Briand, Dessimoz, El-Mabrouk and Nevers (2022).
