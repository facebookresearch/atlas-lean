# Padding entropy and seed sizes in the dictionary tree

In the multi-level dictionary tree, rounding the universe $[U]$ up to $[U']$ increases $\log_2 \binom{U}{n} + n \log_2 V$ by $o(R)$ bits; the child-router seed of a level-$\ell$ node takes $O(n_\ell^{1/25})$ bits, a vanishing fraction of the $\Theta(n_\ell^{7/9})$ bits of the node's waiting list; and, summed over the tree, the minimaps contribute $O(n / r^9)$ redundant bits, the waiting lists $O(n / r^2)$, the non-root storage tables $O(n \log r / r^3)$ and the root storage tables $O(n / \log^2 n)$, each $O(R)$ for $r = n / R$.

## Proof sketch

Since $U' - U < B_0 2^{I_1} = n \cdot \mathrm{polylog}(n)$ and $U \ge n^{1+\alpha_{\min}}$, rounding changes $\log_2 \binom{U}{n}$ by at most $n \log_2(U'/U) = O(n^{1-\alpha_{\min}} \mathrm{polylog}(n))$ bits. The router family of Li, Liang, Yu and Zhou (Lemma 5.1) with $\varepsilon = 1/100$ and $L = I_\ell$ stores a seed in $O(2^{I_\ell/100})$ bits. A level-$\ell$ waiting list holds at most $2\Delta_\ell$ entries of $O(\log n_{\ell-1})$ bits, and there are $n / n_\ell$ such nodes; the other terms are the per-node redundancies of the minimaps and storage tables times the number of nodes (Section 5.2).

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Waiting list of a dictionary-tree node](waiting-list-of-a-node.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
