# Tree realization number of a barcode

**Setting.** A *merge tree* is a rooted tree with a height function, whose sublevel-set components merge as the height increases; its 0-dimensional persistence barcode records, by the elder rule, a bar $[b, d)$ for each branch, born at a leaf height $b$ and dying at the height $d$ where it merges into an older branch, plus one infinite bar $[b_0, \infty)$. A *strict* barcode $B = \{[b_0, \infty)\} \cup \{[b_i, d_i)\}_{i=1}^n$ has distinct endpoints, ordered by $b_0 < b_1 < \dots < b_n$. Its *permutation type* $\sigma(B) \in S_n$ maps birth order to death order. The *tree realization number* $R(B)$ is the number of combinatorial trees $T$ admitting a height function whose barcode is $B$. The *left inversion vector* of $\sigma \in S_n$ is $l_i(\sigma) = \#\{j \le i : \sigma(j) \ge \sigma(i)\}$, $i = 1, \dots, n$.

**Theorem.**
1. *(Index formula.)* $R(B) = \prod_{j=1}^n \mu(I_j)$, where the index $\mu(I_j)$ is the number of other bars of $B$, the infinite bar included, that contain $I_j = [b_j, d_j)$.
2. *(Left inversion vector.)* $R(B) = \prod_{i=1}^n l_i(\sigma(B))$, so $R$ depends only on the permutation type and is constant on combinatorial equivalence classes of barcodes.
3. *(Total count.)* Combinatorial equivalence classes of merge trees with $n+1$ leaves are in bijection with maximal chains in the lattice of set partitions of an $(n+1)$-element set; consequently
$$\sum_{\sigma \in S_n} R(\sigma) = \sum_{\sigma \in S_n} \prod_{i=1}^n l_i(\sigma) = \frac{(n+1)!\,n!}{2^n}.$$
4. *(Random barcodes.)* If $\sigma$ is uniform on $S_n$, the law $\pi_n$ of $R(\sigma)$ satisfies $\pi_1 = U_1$ and $\pi_k = U_k * \pi_{k-1}$, where $U_k$ is uniform on $\{1, \dots, k\}$ and $*$ is Dirichlet convolution, $\pi_k(c) = \sum_{ab = c} U_k(a)\,\pi_{k-1}(b)$; that is, $R(\sigma)$ is distributed as a product of independent uniform variables on $\{1\}, \{1,2\}, \dots, \{1, \dots, n\}$.
5. *(Merge trees versus phylogenetic trees.)* For a combinatorial phylogenetic tree $T$ whose root has unique child $c$, with $A_i$ the internal nodes at distance $i$ from $c$, the number $\eta(T)$ of combinatorial classes of merge trees with underlying phylogenetic tree $T$ satisfies $\eta(T) \ge \prod_{j \ge 0} |A_j|!$.

## Expansion

Building a merge tree from its barcode amounts to deciding, for each dying branch, which older branch alive at its death time it merges into; the candidates are exactly the bars containing it, which gives the product of indices. Sorting bars by birth, these candidates for bar $i$ are the earlier bars dying later, plus the infinite bar, which is the left inversion count. Uniform random permutations have independent left inversion entries with $l_i$ uniform on $\{1, \dots, i\}$, giving the Dirichlet-convolution law. The construction underlies topological morphology descriptors of branching structures such as neuronal arbors, where a barcode summarizes a tree and $R(B)$ measures how many shapes it cannot distinguish.

## Sources

- J. Curry, J. DeSha, A. Garin, K. Hess, "From trees to barcodes and back again II: combinatorial and probabilistic aspects of a topological inverse problem", arXiv:2107.11212 (2021), Proposition 2, Lemma 2, Theorem 2, Proposition 3 and Theorem 3, <https://doi.org/10.48550/arXiv.2107.11212>.
