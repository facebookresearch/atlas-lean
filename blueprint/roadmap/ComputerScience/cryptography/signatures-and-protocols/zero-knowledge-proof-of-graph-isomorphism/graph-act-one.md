# Relabeling an adjacency function by the identity permutation

Let $n \in \mathbb{N}$ and let $G : \{0, \dots, n-1\}^2 \to \mathrm{Bool}$ be **any** Boolean adjacency function: no symmetry or loop restriction is imposed, so directed graphs and graphs with loops are included. For a permutation $\sigma$ of $\{0, \dots, n-1\}$, the [relabeled graph](graph-act.md) is $(\sigma \cdot G)(u, v) = G(\sigma^{-1} u, \sigma^{-1} v)$. Relabeling by the identity permutation leaves every such $G$ unchanged:

$$
1 \cdot G = G .
$$

The simple-graph statement [Relabelling by the identity](map-one-perm.md) concerns a different domain.
