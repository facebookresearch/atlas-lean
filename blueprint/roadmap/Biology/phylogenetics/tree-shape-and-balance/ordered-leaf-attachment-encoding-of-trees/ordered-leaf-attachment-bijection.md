# Ordered leaf attachment bijection

**Setting.** Let $\widehat{\mathcal{RBT}}_n$ be the set of rooted binary tree topologies with $n\ge2$ leaves labeled $0,1,\dots,n-1$ (equivalently, with a linear order on the leaf set). *Canonical internal labels*: each node gets a clade-founder label (a leaf's own label; for an internal node, the minimum of its children's founder labels), and each internal node is then labeled $-b$, where $b$ is the larger of its two children's founder labels. This assigns the labels $-1,\dots,-(n-1)$ bijectively to the internal nodes, and the internal node labeled $-i$ is the one created when leaf $i$ is attached. The *ordered leaf attachment* (OLA) code of a tree is the vector $(a_1,\dots,a_{n-1})$ in which $a_i$ is the label (leaf label $\ge0$ or canonical internal label $<0$) of the node that becomes the sibling of leaf $i$ when leaf $i$ is attached to the tree built on leaves $0,\dots,i-1$.

**Statement.** For every $n\ge2$ the OLA encoding $\Phi$ and decoding $\Psi$ are inverse bijections

$$\Phi:\widehat{\mathcal{RBT}}_n\to \mathcal C_{n-1},\qquad \mathcal C_{n-1}=\{(a_1,\dots,a_{n-1})\in\mathbb Z^{n-1} : -i<a_i<i\},$$

so in particular $|\widehat{\mathcal{RBT}}_n|=|\mathcal C_{n-1}|=\prod_{i=1}^{n-1}(2i-1)=(2n-3)!!$ and $a_1=0$ always. Both directions run in $O(n)$ time. The encoding is stable under deleting the last leaf: the code of the restriction to leaves $0,\dots,k-1$ is the corresponding prefix of the code. A Gibbs walk on codes that resamples one uniformly chosen entry at a time becomes exactly uniform on trees after an expected $\Theta(n\log n)$ steps.

## Expansion

Decoding starts from the single leaf $0$ and, for $i=1,\dots,n-1$, subdivides the parent edge of the node labeled $a_i$ (a leaf if $a_i\ge0$, an internal node if $a_i<0$) with a new internal node labeled $-i$ and hangs leaf $i$ from it. When leaf $i$ is added, the tree has $i$ leaves and $i-1$ internal nodes, hence $2i-1$ possible siblings, which matches the $2i-1$ admissible values $-i<a_i<i$. The canonical labels make this choice recoverable from the final tree, because the internal node labeled $-i$ is exactly the parent of leaf $i$ in the tree restricted to leaves $0,\dots,i$. Since domain and codomain have the same size $(2n-3)!!$, surjectivity proved by induction on $n$ gives the bijection. Canonical labels are computed by one root-ward and one leaf-ward traversal, which gives linear time. The mixing statement is a coupon-collector argument: the walk is uniform once each entry $a_2,\dots,a_{n-1}$ has been resampled at least once.

## Sources

- Harry Richman, Cheng Zhang, Frederick A. Matsen, "Vector encoding of phylogenetic trees by ordered leaf attachment", *Bulletin of Mathematical Biology* 88(4) (2026), 58, Theorem 1, Proposition 6, Theorem 7, Proposition 8, Theorem 9, Theorem 10 and Theorem 11, <https://doi.org/10.1007/s11538-026-01611-9> (preprint arXiv:2503.10169).
