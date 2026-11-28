# Greedy linear-time max-diameter and sum-length tree partitioning

Let $T = (V, E)$ be an unrooted binary tree with nonnegative edge weights $w$, leaf set $L$, and path length $d(u, v)$ between leaves. A partition $\{L_1, \dots, L_N\}$ of $L$ is **admissible** if it is the family of leaf sets of the connected components of $(V, E \setminus C)$ for some cut set $C \subseteq E$. For a cluster-heterogeneity function $f_T : 2^L \to \mathbb{R}$ and threshold $\alpha \ge 0$, the **min-cut partitioning problem** asks for an admissible partition with $f_T(L_i) \le \alpha$ for all $i$ and minimum $N$. Two choices of $f_T$:

- **max-diameter:** $f_T(S) = \max_{u, v \in S} d(u, v)$;
- **sum-length:** $f_T(S) = \sum_{e \in \mathrm{edges}(T|_S)} w(e)$, the total branch length of the subtree spanned by $S$.

**Algorithm (max-diameter).** Root $T$ arbitrarily at a node $o$. Set $B(v) = 0$ for every leaf. Visit internal nodes $u$ in post-order, with children $u_l, u_r$ and child-edge weights $w_l, w_r$:

- if $B(u_l) + w_l + B(u_r) + w_r > \alpha$, cut the child edge with the larger value of $B(\cdot) + w_\cdot$ and set $B(u)$ to the smaller of $B(u_l) + w_l$ and $B(u_r) + w_r$;
- otherwise set $B(u) = \max(B(u_l) + w_l, B(u_r) + w_r)$.

Return the leaf sets of the connected components. Here $B(u)$ is the distance from $u$ to the farthest leaf still connected to $u$ inside its subtree.

**Theorem.** For the rooted tree $T_o$, the algorithm produces the minimum number of clusters of diameter at most $\alpha$, and among all such optimal clusterings it minimizes $B(o)$. Consequently, the cut set obtained from an arbitrary rooting optimally solves the max-diameter min-cut partitioning problem on the unrooted tree. The running time is $O(|V|)$.

**Sum-length variant.** With $B(u)$ redefined as the total weight of descendant edges still connected to $u$, the same post-order scheme (when $B(u_l) + w_l + B(u_r) + w_r > \alpha$ cut the child edge with the larger $B(\cdot) + w_\cdot$; otherwise set $B(u) = B(u_l) + w_l + B(u_r) + w_r$) solves the sum-length problem optimally in linear time.

**Clade constraint.** On a rooted tree, requiring each cluster to be a clade is enforced by cutting *both* child edges whenever $B(u_l) + w_l + B(u_r) + w_r > \alpha$; the problems remain linear-time.

## Expansion

When $T$ is ultrametric, cutting at height $\alpha/2$ already yields clusters of diameter at most $\alpha$; the min-cut formulation handles non-ultrametric trees. The exchange argument behind the theorem: at node $u$ the only new leaf-to-leaf paths have maximal length $B(u_l) + w_l + B(u_r) + w_r$, so if this exceeds $\alpha$ some child edge must be cut; cutting the longer side leaves the smallest residual $B(u)$, which dominates any alternative for all ancestors, while the cluster count below $u$ cannot be lowered (induction on post-order). Since every cluster of an admissible partition is connected, optimality for one rooting gives optimality for the unrooted tree. The max-diameter problem with unit weights and the node-weighted sum problem were solved earlier in the theoretical computer science literature; the edge-weighted versions apply to phylogenies for OTU picking, transmission clustering and divide-and-conquer alignment.

## Sources

- M. Balaban, N. Moshiri, U. Mai, X. Jia, S. Mirarab, "TreeCluster: Clustering biological sequences using phylogenetic trees", PLoS ONE 14 (2019) e0221068, Materials and methods: Definitions 1–3, Algorithm 1, Theorem 1, Corollary 1, sum-length algorithm and clade constraint, <https://doi.org/10.1371/journal.pone.0221068> (PMC6705769).
