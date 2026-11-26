# Monotone ranged hash functions are permutation hash functions

A [ranged hash function](ranged-hash-functions.md) $f$ on a finite set $\mathcal B$ of buckets is monotone if and only if it is a $\pi$-hash function: there is, for every item $i$, a permutation $\pi(i) = (b_1, b_2, \dots)$ of $\mathcal B$ such that $f_{\mathcal V}(i)$ is the first element of $\pi(i)$ in $\mathcal V$ for every view $\mathcal V$. For a monotone $f$ one takes $b_1 = f_{\mathcal B}(i)$ and $b_{j+1} = f_{\mathcal B \setminus \{b_1, \dots, b_j\}}(i)$; if $b_j$ is the first element of a view $\mathcal V_1$ in this list, then $\mathcal V_1 \subseteq \mathcal V_2 = \mathcal B \setminus \{b_1, \dots, b_{j-1}\}$ and $f_{\mathcal V_2}(i) = b_j \in \mathcal V_1$, so monotonicity gives $f_{\mathcal V_1}(i) = b_j$. Conversely every $\pi$-hash function is monotone.

## Depends on

- [Ranged hash functions](ranged-hash-functions.md)

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.4, Theorem 4.3 and its proof sketch.
