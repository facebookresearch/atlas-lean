# Single-linkage min-cut partitioning of a tree

Let $T = (V, E)$ be an unrooted binary weighted tree with leaf set $L$, leaf distance $d$, and threshold $\alpha$. A partition of $L$ is the **single-linkage clustering** at level $\alpha$ if leaves $a, b$ lie in the same cluster exactly when there is a chain $a = c_0, c_1, \dots, c_{m+1} = b$ of leaves with $d(c_i, c_{i+1}) \le \alpha$ for all $i$. The **single-linkage min-cut partitioning problem** is the min-cut partitioning problem (fewest admissible clusters obtained by deleting edges, see [greedy max-diameter partitioning](greedy-max-diameter-and-sum-length-tree-partitioning.md)) with cluster criterion

$$f_T(S) = \max_{\emptyset \ne R \subsetneq S} \; \min_{u \in R,\, v \in S \setminus R} d(u, v) \le \alpha ,$$

i.e. no split of a cluster into two parts has a gap larger than $\alpha$.

**Proposition.** The optimal solution of the single-linkage min-cut partitioning problem is identical to the single-linkage clustering at level $\alpha$.

**Linear-time algorithm.** Root $T$ at $o$. In post-order compute $\mathrm{minBelow}(u)$, the distance from $u$ to its nearest descendant leaf ($0$ at leaves, $\min(\mathrm{minBelow}(u_l) + w_l,\, \mathrm{minBelow}(u_r) + w_r)$ otherwise). In pre-order compute $\mathrm{minAbove}(u)$, the distance from $u$ to the nearest leaf outside its subtree: for $u$ with parent $v$ and sibling $s$, $\mathrm{minAbove}(u) = w(v, u) + \min(\mathrm{minBelow}(s) + w(v, s),\, \mathrm{minAbove}(v))$, with $\mathrm{minAbove}(o) = \infty$. Then, in post-order over internal $u$, cut a child edge (or the parent edge) exactly when *both* ways of joining the leaves below it to the rest (to the sibling subtree, or to leaves outside $u$) have nearest-leaf distance exceeding $\alpha$.

**Theorem.** This partitioning solves the single-linkage min-cut partitioning problem optimally, in $O(|V|)$ time.

## Depends on

- [Greedy linear-time max-diameter and sum-length tree partitioning](greedy-max-diameter-and-sum-length-tree-partitioning.md)

## Expansion

Single-linkage chaining relaxes the diameter constraint: two leaves at distance greater than $\alpha$ may share a cluster if a chain of close leaves connects them. In a tree, the closest pair of leaves on opposite sides of an edge is determined by the two nearest-leaf distances at the edge's endpoints, so the chaining relation can be decided edge by edge from $\mathrm{minBelow}$ and $\mathrm{minAbove}$. An edge whose removal separates leaves with no cross pair within $\alpha$ must be cut by any feasible partition, and cutting only those edges yields connected components that are precisely the single-linkage classes, which gives both the proposition and optimality.

## Sources

- M. Balaban, N. Moshiri, U. Mai, X. Jia, S. Mirarab, "TreeCluster: Clustering biological sequences using phylogenetic trees", PLoS ONE 14 (2019) e0221068, Materials and methods: Definitions 4–5, Proposition 1, Algorithm 2, Theorem 2, <https://doi.org/10.1371/journal.pone.0221068> (PMC6705769).
