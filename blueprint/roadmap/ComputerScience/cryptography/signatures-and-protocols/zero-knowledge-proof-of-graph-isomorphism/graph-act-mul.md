# Relabeling an adjacency function by a product of permutations

Let $n \in \mathbb{N}$ and let $G : \{0, \dots, n-1\}^2 \to \mathrm{Bool}$ be **any** Boolean adjacency function: no symmetry or loop restriction is imposed, so directed graphs and graphs with loops are included. For a permutation $\sigma$ of $\{0, \dots, n-1\}$, the [relabeled graph](graph-act.md) is $(\sigma \cdot G)(u, v) = G(\sigma^{-1} u, \sigma^{-1} v)$. For all permutations $\sigma, \tau$ and every such $G$, relabeling by $\tau$ and then by $\sigma$ is relabeling by the product $\sigma\tau$ ($\tau$ applied first):

$$
\sigma \cdot (\tau \cdot G) = (\sigma\tau) \cdot G .
$$

Together with [relabeling by the identity](graph-act-one.md), this makes relabeling an action of the permutation group on all adjacency functions. The simple-graph statement [Composing relabellings](map-map-perm.md) concerns a different domain.
