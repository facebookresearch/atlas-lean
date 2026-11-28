# Karger's contraction algorithm on the randomized word RAM

There is a randomized word-RAM program implementing Karger's Contraction Algorithm on an $n$-vertex weighted multigraph ($n \ge 2$) given by its symmetric weight matrix that runs one trial in $O(n^2)$ instructions; every run outputs the weight of a nontrivial cut, and a trial outputs the minimum cut weight with probability at least $2/(n(n-1))$. Consequently $R$ independent trials run in $O(Rn^2)$ instructions and all miss the minimum cut weight with probability at most $(1 - 2/(n(n-1)))^R$, and in particular $R = \lceil \tfrac12 n(n-1)\ln(2n) \rceil = O(n^2 \log n)$ trials, $O(n^4 \log n)$ instructions in total, miss it with probability at most $1/(2n)$, so they find it with probability exceeding $1 - 1/n$.

## Proof sketch

Karger and Stein implement one trial with the weight matrix $W$ and weighted degrees $D$ (Section 3): an edge is chosen with probability proportional to its weight by choosing an endpoint $u$ with probability proportional to $D(u)$ and then $v$ with probability proportional to $W(u, v)$ (Lemma 3.1), and contracting $u$ and $v$ merges two rows and columns; each step takes $O(n)$ time, so a trial takes $O(n^2)$ (Corollary 3.2). On the randomized word RAM each proportional choice is one $\mathrm{rand}$ draw over a cumulative weight array followed by a binary search, so the $O(n)$ bound per step holds for every run, not only in expectation. The run ends with two super-vertices $u, v$, whose sides are both nonempty, and outputs $W(u, v)$, the weight of that cut. A fixed minimum cut survives all $n - 2$ contractions with probability at least $\binom{n}{2}^{-1} = 2/(n(n-1))$ (Theorem 2.2, and Corollary 2.4 for weights). Independent trials miss with probability at most $(1 - p)^R \le e^{-pR}$ for $p = 2/(n(n-1))$; for example $R = \lceil \tfrac12 n(n-1) \ln(2n) \rceil$ trials give failure probability at most $1/(2n)$.

## Depends on

- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Edge contraction](../karger-s-algorithm/contract.md)
- [Minimum cut size](../karger-s-algorithm/is-min-cut.md)

## Proof depends on

- [Each minimum cut survives with probability at least $2/(n(n-1))$](../karger-s-algorithm/survive-prob-ge.md)

## Sources

- D. R. Karger, "Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut Algorithm", Proceedings of the 4th ACM-SIAM Symposium on Discrete Algorithms (SODA), 1993.
- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996, Section 1.6, Theorem 2.2, Corollary 2.4, Lemma 3.1 and Corollary 3.2.
