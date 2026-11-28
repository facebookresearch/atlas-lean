# Maximum agreement subtree of two trees in polynomial time

Given a set $S = \{S_1, \dots, S_n\}$ and two trees $P$ and $Q$ leaf-labelled by the elements of $S$, the maximum agreement subtree problem, posed by Finden and Gordon, asks for a maximum-cardinality subset $S_0 \subseteq S$ such that the restrictions agree, $P|S_0 = Q|S_0$. Steel and Warnow (1993) give an algorithm computing the size of a largest agreement subtree of two trees on $n$ leaves in time $O(n^{4.5}\log n + V)$, where $V$ is the maximum number of nodes in the trees, and, for trees of maximum degree $k$, two algorithms with running times $O(k!\,n^2 + V)$ and $O(k^{2.5} n^2\log n + V)$. The algorithms also apply when the trees are rooted, the agreement subtree then being rooted as well, and each can be modified to output a maximum agreement subtree within the same running time. A superpolynomial-time algorithm for a maximum agreement subtree of two binary trees had been given earlier by Kubicka and coauthors.

## Expansion

1. Definitions: restriction of a leaf-labelled tree to a subset of its labels (with vertices of degree two suppressed), agreement subtrees, and the rooted and unrooted versions.
2. A dynamic program over pairs of rooted subtrees of $P$ and $Q$ computing the largest agreement subtree for each pair.
3. The combination step at a pair of vertices as a weighted bipartite matching between their children, as the source of the $n^{4.5}\log n$ and $k^{2.5}n^2\log n$ bounds, and exhaustive search over child correspondences for the $k!\,n^2$ bound.
4. The reduction of the unrooted problem to rooted instances.
5. Recovery of an optimal subset from the table, giving the search version in the same time.

## Sources

- M. Steel and T. Warnow, Kaikoura tree theorems: computing the maximum agreement subtree, Inform. Process. Lett. 48 (1993), 77–82, abstract. <https://doi.org/10.1016/0020-0190(93)90181-8>
