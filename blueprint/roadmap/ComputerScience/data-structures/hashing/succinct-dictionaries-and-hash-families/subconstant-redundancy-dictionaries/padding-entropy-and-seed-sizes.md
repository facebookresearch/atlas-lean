# Padding entropy and seed sizes in the dictionary tree

In the multi-level dictionary tree, rounding the universe $[U]$ up to $[U']$ increases $\log_2 \binom{U}{n} + n \log_2 V$ by $o(R)$ bits; the child-router seed of a level-$\ell$ node takes $O(n_\ell^{1/25})$ bits and each per-child identifier permutation $O(I_\ell)$ bits, for a non-root node a vanishing fraction of the $O(n_\ell^{7/9})$ bits of its waiting list (for a root, of the redundancy of its storage table); and, summed over the tree, the minimaps contribute $O(n / r^9)$ redundant bits, the waiting lists $O(n / r^2)$, the non-root storage tables $O(n \log r / r^3)$ and the root storage tables $O(n / \log^2 n)$, each $O(R)$ for $r = n / R$.

## Proof sketch

Since $U' - U < B_0 2^{I_1} = n \cdot \mathrm{polylog}(n)$ and $U \ge n^{1+\alpha_{\min}}$, rounding changes $\log_2 \binom{U}{n}$ by at most $\sum_{i<n} \log_2 \frac{U' - i}{U - i} \le n \log_2 \frac{U' - n + 1}{U - n + 1} \le \frac{n (U' - U)}{(U - n + 1) \ln 2} = O(n^{1-\alpha_{\min}} \mathrm{polylog}(n))$ bits, since $U - n + 1 \ge U/2$. The router family of Li, Liang, Yu and Zhou (Lemma 5.1) with $\varepsilon = 1/100$ and $L = I_\ell$ stores a seed in $O(2^{I_\ell/100}) = O(n_\ell^{1/25})$ bits, and Lemma 5.2 stores an identifier permutation in $O(I_\ell)$ bits. A level-$\ell$ waiting list holds at most $2\Delta_\ell$ entries of $O(\log n_{\ell-1})$ bits, and there are $n / n_\ell$ such nodes; the other terms are the per-node redundancies of the minimaps and storage tables times the number of nodes (Section 5.2). The source does not analyse the rounding of $U$; that bound is the computation above.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Waiting list of a dictionary-tree node](waiting-list-of-a-node.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
