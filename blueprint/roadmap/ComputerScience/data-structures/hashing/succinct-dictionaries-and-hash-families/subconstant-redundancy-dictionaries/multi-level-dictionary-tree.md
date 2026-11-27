# Multi-level dictionary tree with subconstant wasted bits

Fix constants $0 < \alpha_{\min} \le \alpha_{\max}$, write $\log$ for $\log_2$ and $\log^{(\ell)}$ for the $\ell$-fold iterated logarithm, and let $n$ keys of a universe $[U]$ with $n^{1+\alpha_{\min}} \le U \le n^{1+\alpha_{\max}}$ carry values in $[V]$, with redundancy parameter $R$ in the range $n / \log^{0.1} n \le R \le n / 2^{\log^* n}$, on a word RAM with $w = \Omega(\log(UV))$. As in the source, the dictionary always holds $n$ or $n - 1$ keys. Let $r = n / R$ and let $k$ be the level with $\log^{(k)} n \le r < \log^{(k-1)} n$. The *multi-level dictionary tree* (Li, Liang, Yu and Zhou, Section 5) is the following forest of depth $k$.

- **Schedule.** There are $B_0$ roots at level $1$, and every node at level $\ell < k$ has $B_\ell$ children. Every $B_\ell$ is a power of two, and the expected loads $n_0 = n$ and $n_\ell = n_{\ell-1} / B_{\ell-1}$ satisfy $n_\ell \in [(\log^{(\ell)} U)^9, 2 (\log^{(\ell)} U)^9)$ for $1 \le \ell \le k - 1$ and $n_k \in [r^9, 2 r^9)$; these conditions determine the $B_\ell$.
- **Capacities.** With $\Delta_\ell = n_\ell^{2/3}$, let $\underline{n}_\ell = \lceil n_\ell - \Delta_\ell \rceil$ and $\overline{n}_\ell = \lfloor n_\ell + \Delta_\ell \rfloor$. A level-$\ell$ node *overflows* if more than $\overline{n}_\ell$ keys are hashed into it and *underflows* if fewer than $\underline{n}_\ell$ are.
- **Routing.** The universe is rounded up to a multiple $U'$ of $B_0 2^{I_1}$; the elements of $[U'] \setminus [U]$ are *sentinel* keys. At a level-$\ell$ node a key is a pair of an identifier in $[2^{I_\ell}]$, with $I_\ell = \lceil 4 \log n_\ell \rceil$, and a quotient. A one-round Feistel permutation of the identifier, whose round function is drawn from Thorup's highly independent family, sends the key to a child $v \in [B_\ell]$ and a primitive identifier, and a second Feistel permutation chosen per child, whose round function is drawn from a $2$-wise independent family, splits that into the identifier in $[2^{I_{\ell+1}}]$ and bits appended to the quotient. Keys are sent to the roots in the same way by a top-level router on $[U']$. A seed assignment is *good* when no node overflows or underflows and, at every node, the keys sent to each child receive distinct identifiers.
- **Storage.** Every stored key is kept as its identifier at the storing node together with its payload: its quotient at that level and its dictionary value in $[V]$ (the source treats the quotient as the value of the identifier and values as payload carried with the key). Each leaf stores exactly $\underline{n}_k$ of its keys in a fixed-capacity minimap on identifiers in $[2^{I_k}]$ with these payloads as values. Each non-root node at level $\ell < k$ stores exactly $\underline{n}_\ell - B_\ell \underline{n}_{\ell+1}$ of the keys its children return in a full storage table (a fixed-capacity succinct hash table of Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul and Liu, with $O(m \log I_\ell)$ bits of redundancy for capacity $m$), so that its subtree stores exactly $\underline{n}_\ell$ keys; each root stores the keys returned to it in a storage table of capacity $\overline{n}_1 - B_1 \underline{n}_2$. Keys not stored at a node are returned to its parent.
- **Waiting lists.** Every non-root node at level $\ell$ keeps a waiting list of capacity $\overline{n}_\ell - \underline{n}_\ell \le 2 \Delta_\ell$ (see the waiting-list page).
- **Rebuilding.** When a node overflows or underflows, the subtree of its parent is rebuilt with a fresh child router for the parent, and the whole dictionary when a root does; when two keys sent to a child $v$ receive the same identifier, the subtree of $v$ is rebuilt with a fresh identifier permutation for $v$.

## Depends on

- [Minimap of a fixed-capacity leaf](minimap-of-a-leaf.md)
- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)
- [Iterated logarithm and log-star](../dictionary-specifications/iterated-logarithm.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), pp. 1284-1297, 2022.
