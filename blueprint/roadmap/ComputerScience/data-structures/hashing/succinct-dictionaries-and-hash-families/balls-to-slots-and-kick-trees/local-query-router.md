# Local query router by binary prefix trie

The *query-router problem*: maintain a set $S$ of distinct keys and a function $f : S \to \mathbb{N}$ with distinct values, under insertions (add $s$ with $f(s) := u$), deletions and evaluation queries "what is $f(s)$ for $s \in S$", given $|S| = O(\log n / \log\log n)$ at all times, $f(s)$ of $O(\log\log n)$ bits, and a constant-time oracle for $g = f^{-1}$ (so keys need not be stored). With $r = |S| + \sum_{s \in S} \log f(s)$, a *local query router* solves it in $O(1)$ time per operation with high probability in $n$, using $O(r)$ bits in expectation and $O(\log n)$ bits with high probability in $n$ at any given moment. It hashes the keys of $S$ to random binary strings, keeps the binary trie of their shortest unique prefixes (expected size $O(|S|)$), and encodes it as the move sequence of a depth-first traversal followed by the values $f(s)$ in leaf order; operations are performed on this encoding with lookup tables. It is rebuilt every $O(\log n / \log\log n)$ operations, and $O(1)$ independent copies amplify the per-operation failure probability $n^{-\varepsilon}$ to $1/\mathrm{poly}(n)$.

## Depends on

- [Rank and select on small bit vectors by table lookup](rank-and-select-by-table-lookup.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 4.3, Lemma 15).
