# Semi-streaming graph model with insertion-only, dynamic and random-order edge streams

Fix a vertex set $V$ with $|V| = n$. An *insertion-only graph stream* of a simple undirected graph $G = (V, E)$ is a sequence $e_1, \dots, e_m$ listing every edge of $E$ exactly once, in an order chosen by an adversary. A *random-order stream* lists $E$ in the order of a uniformly random permutation of $E$, independent of the coins of the algorithm. A *dynamic graph stream* is a sequence of updates $(e_t, \sigma_t)$ with $e_t \in \binom{V}{2}$ and $\sigma_t \in \{+1, -1\}$ such that after every prefix the accumulated multiplicity of each pair lies in $\{0, 1\}$; the input graph is the set of pairs with final multiplicity $1$.

A *$p$-pass semi-streaming algorithm* is a randomized streaming algorithm that reads the stream $p$ times in the given order and keeps at most $n \log^{c} n$ bits of memory between updates, for an absolute constant $c$; when a bound also depends on an accuracy parameter $\varepsilon$, that dependence (for example a factor $\mathrm{poly}(1/\varepsilon)$) is stated explicitly. An algorithm succeeds *with high probability* if its output is correct with probability at least $1 - n^{-c'}$ for a constant $c' > 0$.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)

## Sources

- Sepehr Assadi, Aaron Bernstein, "Towards a Unified Theory of Sparsification for Matching Problems", SOSA (2019), arXiv:1811.02009.
- Aaron Bernstein, "Improved Bounds for Matching in Random-Order Streams", ICALP (2020), arXiv:2005.00417.
