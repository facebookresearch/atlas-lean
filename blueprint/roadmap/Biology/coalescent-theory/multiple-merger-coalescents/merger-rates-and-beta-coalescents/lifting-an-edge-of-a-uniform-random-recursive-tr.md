# Uniformity after lifting an edge of a random recursive tree

Let $n\ge1$ and let $\pi=(B_1,\ldots,B_b)$ be a partition of $[n]$
into nonempty blocks, ordered by least element.
A recursive tree on these blocks is rooted at $B_1$ and every child's
block index is larger than its parent's. There are exactly $(b-1)!$
such trees; independently choosing the parent of $B_j$ uniformly among
$B_1,\ldots,B_{j-1}$, for $2\le j\le b$, gives their uniform law.

For $b\ge2$, sample such a tree and choose $J$ uniformly in
$\{2,\ldots,b\}$ independently of it; choose the edge from $B_J$ to
its parent. This is the precise meaning of a uniform edge conditional
on the tree. Lift it by deleting the entire subtree rooted at $B_J$
and adjoining all of that subtree's block labels to the parent label.
All other edges are retained. Conditional on the resulting coarser
partition $\pi'$, the resulting tree is uniform among recursive trees
on $\pi'$. If $b=1$, there is no edge to choose or lift, even when
$n>1$.

## Expansion

Fix a set $S$ of $k\ge2$ old blocks to merge, and a particular output
tree $t'$ on the coarsened partition. Write $i_1<i_2<\cdots<i_k$ for
their indices. The old parent must be $B_{i_1}$, and the deleted subtree
must be rooted at $B_{i_2}$ and contain exactly the other $k-1$ blocks.
There are $(k-2)!$ recursive trees on that deleted label set.
For each, restore the merged label in $t'$ to $B_{i_1}$ and attach the
deleted tree's root to it. These are exactly the preimages, with exactly
one chosen edge each. Therefore

$$\mathbb P(\pi'=\pi_S,\ T'=t')
 =\frac{(k-2)!}{(b-1)!(b-1)}.$$

There are $(b-k)!$ possible $t'$, so this joint probability is constant
over them, proving conditional uniformity. It also gives
$\mathbb P(\pi'=\pi_S)=(k-2)!(b-k)!/((b-1)!(b-1))$ for any specified
$k$-subset of blocks. This is a statement about blocks, regardless of
their sizes as subsets of $[n]$.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 6.1.1, Definitions 6.2–6.3, Lemma 6.1 and equations (156)–(157).
- C. Goldschmidt and J. B. Martin, *Random recursive trees and the Bolthausen–Sznitman coalescent*, EJP 10 (2005), 718–745, <https://doi.org/10.1214/EJP.v10-265>, original attribution via Berestycki. The full finite preimage count is given above.
