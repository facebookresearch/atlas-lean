# Karger's contraction algorithm on the randomized word RAM

There is a randomized word-RAM program implementing Karger's contraction on an $n$-vertex weighted multigraph with three endpoints: a single trial halts within $42n^2 + 12n + 21$ instructions and outputs the minimum cut weight with probability at least $2/(n(n-1))$; $R$ independent trials halt within $R(50n^2 + 12n + 30) + 16$ instructions and miss the minimum with probability at most $(1 - 2/(n(n-1)))^R$; and a high-probability version halts within $33 n^4 (\lfloor \log_2 n \rfloor + 2)$ instructions and misses the minimum cut with probability at most $1/(2n)$. Every run outputs the weight of a genuine nontrivial cut.

## Depends on

- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [Edge contraction](../karger-s-algorithm/contract.md)
- [Minimum cut size](../karger-s-algorithm/is-min-cut.md)

## Proof depends on

- [Each minimum cut survives with probability at least $2/(n(n-1))$](../karger-s-algorithm/survive-prob-ge.md)

## Sources

- D. R. Karger, "Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut Algorithm", Proceedings of the 4th ACM-SIAM Symposium on Discrete Algorithms (SODA), 1993.
- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996.
