# The exhaustive history has the fewest phrases

For every word $x$ and window size, the exhaustive (greedy) parsing is a history of $x$, and its number of phrases is at most the number of phrases of every history of $x$ with the same window. The minimum number of phrases is the **Lempel-Ziv complexity** of $x$.

## Proof sketch

By induction on phrases: after $i$ phrases the greedy history has covered at least as long a prefix as any history, because reproducibility is closed under taking prefixes and under extending the already-written text.

## Depends on

- [Reproducible phrases and Lempel-Ziv histories](lempel-ziv-histories.md)

## Sources

- A. Lempel and J. Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1), 1976.
