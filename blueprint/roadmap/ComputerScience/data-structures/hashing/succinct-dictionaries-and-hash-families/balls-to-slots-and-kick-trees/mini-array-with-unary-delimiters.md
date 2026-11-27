# Mini-array with unary delimiters

Let $c$ be a sufficiently large constant and $K = \log^c n$. A *mini-array* stores entries $A[1], \dots, A[K]$ of variable sizes $s_i \in [0, O(\log n)]$ bits, supporting the query "return $A[i]$" and the update "set $A[i]$ to a new value" (which may change $s_i$). It is implemented as a B-tree of $\mathrm{polylog}\, n$ nodes of $\Theta(\log n)$ bits each (the root may be smaller), with internal fanout $\Theta(\log n / \log\log n)$, $\Theta(\log\log n)$-bit child pointers, and for each child the range of indices it covers; each leaf holds a consecutive block $A[i], \dots, A[j]$ of entries with $\sum_{\ell=i}^{j} (s_\ell + 1) = \Theta(\log n)$ as array bits, together with a bitmap marking where each entry begins. Nodes split and merge as in a standard B-tree, so the depth is $O(1)$. Queries and updates take deterministic $O(1)$ time using lookup tables of $\tilde O(\sqrt{n})$ bits shared by all mini-arrays, and the mini-array uses $O(K + \sum_i s_i)$ bits.

## Depends on

- [Rank and select on small bit vectors by table lookup](rank-and-select-by-table-lookup.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 4.2).
