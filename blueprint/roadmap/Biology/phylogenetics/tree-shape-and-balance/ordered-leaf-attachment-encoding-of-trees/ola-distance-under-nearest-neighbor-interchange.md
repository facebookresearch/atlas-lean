# OLA distance under nearest-neighbor interchange

**Setting.** Let $\widehat{\mathcal{RBT}}_n$ be the set of rooted binary tree topologies with $n\ge2$ leaves labeled $0,1,\dots,n-1$ (equivalently, with a linear order on the leaf set). *Canonical internal labels*: each node gets a clade-founder label (a leaf's own label; for an internal node, the minimum of its children's founder labels), and each internal node is then labeled $-b$, where $b$ is the larger of its two children's founder labels. This assigns the labels $-1,\dots,-(n-1)$ bijectively to the internal nodes, and the internal node labeled $-i$ is the one created when leaf $i$ is attached. The *ordered leaf attachment* (OLA) code of a tree is the vector $(a_1,\dots,a_{n-1})$ in which $a_i$ is the label (leaf label $\ge0$ or canonical internal label $<0$) of the node that becomes the sibling of leaf $i$ when leaf $i$ is attached to the tree built on leaves $0,\dots,i-1$.

The *OLA distance* $d_{\mathrm{OLA}}(T,T')$ between two trees in $\widehat{\mathcal{RBT}}_n$ is the Hamming distance between their OLA codes.

**Statement.** Let $n\ge4$, let $T\in\widehat{\mathcal{RBT}}_n$ be fixed and let $T'$ be obtained from $T$ by a nearest-neighbor interchange (NNI) move chosen uniformly at random among the NNI moves of $T$. Then

$$\mathbb E\bigl[d_{\mathrm{OLA}}(T,T')\bigr]\le 4 .$$

In the worst case, however, a single NNI move can change $n-2$ of the $n-1$ entries, the maximum possible since $a_1=0$ for every tree; so $d_{\mathrm{OLA}}$ is not within a constant factor of the NNI distance. For subtree prune and regraft (SPR) moves it is conjectured that $\mathbb E[d_{\mathrm{OLA}}(T,T')]=O(\mathrm{height}(T))$.

## Depends on

- [Ordered leaf attachment bijection](ordered-leaf-attachment-bijection.md)

## Expansion

An NNI move contracts an internal edge between nodes with canonical labels $-j$ and $-k$ (with $-k$ above) and re-expands it in one of the two other ways. If after the move the upper node still carries label $-k$, only the entry $a_j$ changes, so the distance is exactly $1$. If the labels swap, the changed entries are $a_j$, $a_k$, or entries $a_\ell=-k$ of leaves attached just above the modified edge, so $d_{\mathrm{OLA}}(T,T')\le 1+c_k$, where $c_k$ is the number of entries of the code of $T$ equal to $-k$. A tree with $n$ leaves has $2n-4$ NNI neighbours and at most four of them have upper node $-k$, while $\sum_k c_k\le n-1$. Hence

$$\mathbb E\bigl[d_{\mathrm{OLA}}(T,T')\bigr]\le 1+\frac{4}{2n-4}\sum_k c_k\le 1+\frac{4n-4}{2n-4}\le 4\quad (n\ge4).$$

The worst case is a caterpillar-like tree in which swapping the two lowest internal labels changes the recorded sibling of every later leaf.

## Sources

- Harry Richman, Cheng Zhang, Frederick A. Matsen, "Vector encoding of phylogenetic trees by ordered leaf attachment", *Bulletin of Mathematical Biology* 88(4) (2026), 58, Definition 2, Theorem 3 and Conjecture 5, <https://doi.org/10.1007/s11538-026-01611-9> (preprint arXiv:2503.10169).
