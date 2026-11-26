# Succinct variable-order de Bruijn graph: space and time bounds

Let a $K$-th order de Bruijn graph with $n$ nodes over an alphabet of constant size $\sigma=O(1)$ be stored in the BOSS representation (a wavelet tree over the edge-label column $W$ and a bitvector $L$ marking the ends of node intervals). Let $L^*[i]$ be the length of the longest common suffix of the $K$-character labels of the nodes containing rows $i$ and $i+1$; entries equal to $K$ occur only inside a node interval and may be omitted.

**Theorem.** A variable-order de Bruijn graph, supporting the queries $\mathsf{forward}$, $\mathsf{backward}$ and $\mathsf{lastchar}$ at every order $k\le K$, can be stored in

- $O(n\log K)$ bits on top of the BOSS representation, with $\mathsf{forward}$ and $\mathsf{backward}$ in $O(\log K)$ time and $\mathsf{lastchar}$ in $O(1)$ time; or
- $O(n)$ bits on top of the BOSS representation, with $\mathsf{forward}$ and $\mathsf{backward}$ in $O(K\log n/\log\log n)$ time.

## Expansion

$\mathsf{maxlen}([i,j],a)$ takes $O(\log\sigma)$ time: find an occurrence of $a$ in $W[i..j]$ by rank/select, then expand to the enclosing node interval with rank/select on $L$; $\mathsf{maxlen}(v,*)$ takes $O(1)$. Since a lower-order node is a maximal row interval whose boundaries have common-suffix length below $k$, $\mathsf{shorter}([i,j],k)$ is the largest $i'\le i$ and smallest $j'\ge j$ with $L^*[i'-1],L^*[j']<k$, and $\mathsf{longer}([i,j],k)$ reports the consecutive gaps of $\{b\in[i-1,j]:L^*[b]<k\}$. A wavelet tree over $L^*$ answers both in $O(\log K)$ per reported node using $O(\log K)$ bits per $K$-th order node. Through the reduction of variable-order queries to $K$-th order ones, this gives the first bound. For the second, $L^*$ is not stored: any entry is recomputed from labels by $O(K)$ calls to $\mathsf{backward}$ and $\mathsf{lastchar}$, and a $2n+o(n)$-bit range-minimum structure over $L^*$ locates the boundaries.

## Depends on

- [Variable-order navigation by suffix truncation of a BOSS de Bruijn graph](variable-order-navigation-by-suffix-truncation-of-a-boss-de-bruijn-graph.md)

## Sources

- C. Boucher, A. Bowe, T. Gagie, S. J. Puglisi and K. Sadakane, *Variable-order de Bruijn graphs*, arXiv:1411.2718 (2014), Section 5 and Theorem 1. <https://doi.org/10.48550/arXiv.1411.2718>
