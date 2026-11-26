# NNI connectivity of unrooted tree-based networks

**Definitions.** An unrooted binary phylogenetic network $N$ on leaf set $X$ ($|X|=n$) has **tier** $k$ if $k$ is the minimal number of edges whose deletion leaves a tree; $N(n,k)$ is the set of such networks. A *support tree* of $N$ is a spanning tree whose leaf set is exactly $X$; $N$ is **tree-based** if it has one, and $\mathrm{TBN}(n,k)$ denotes the tree-based networks of tier $k$. A **nearest neighbor interchange** (NNI) on a path $(a,b,c,d)$ swaps the subnetworks attached at $b$ and $c$ across the edge $\{b,c\}$; it preserves the tier. A **triangle move** replaces an interior vertex by a 3-cycle (raising the tier by one) or contracts a 3-cycle (lowering it by one).

**Theorem.**

*(1)* For every $n$ and $k$, $\mathrm{TBN}(n,k)$ is connected under NNI moves that never leave $\mathrm{TBN}(n,k)$.

*(2)* Its NNI diameter is at most

$$f(n,k)=\binom{k-1}{2}+\binom{n-2}{2}+4nk+4k^2+4n-4k-17,$$

so it is $O((n+k)^2)$, and $O(n^2)$ for fixed tier.

*(3)* Triangle moves map tree-based networks to tree-based networks of the adjacent tier, so the space of all tree-based networks on $X$ is connected under NNI and triangle moves, and the distance between networks of fixed tiers $k_1\le k_2$ is $O(n^2)$.

## Expansion

An NNI on $(a,b,c,d)$ keeps a support tree if all three edges are in the support tree, or if only the middle edge $\{b,c\}$ is (among other cases), which gives a supply of tree-basedness-preserving moves. Using them, any tree-based network is first moved to a *lineal* one, whose support tree is a single path between two leaves with all other leaves attached directly to it; lineal networks are then moved to *shoat* networks, a rigid pseudo-Hamiltonian normal form in which a path from leaf $x$ to leaf $y$ visits every interior vertex; finally any two shoat networks of the same tier are connected. Counting the moves in each stage gives the quadratic diameter bound. This matters for search algorithms over network space, which need a connected move graph to reach the optimum without leaving the tree-based class.

## Sources

- Mareike Fischer, Andrew Francis, "The space of tree-based phylogenetic networks", arXiv:1910.05679 (2019), Lemmas 3.1–3.4, Theorem 4.1, Corollary 4.2, Lemma 4.3, Theorem 4.4 and Corollary 4.5, <https://doi.org/10.48550/arXiv.1910.05679>.
