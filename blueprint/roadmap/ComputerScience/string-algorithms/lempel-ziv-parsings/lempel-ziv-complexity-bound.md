# Lempel-Ziv complexity is O(n / log n)

Over an alphabet of size $k \ge 2$, let $x$ be a word of length $n \ge 2$ and let the window size be at least $n$, so that the window covers $x$ and histories are those of the unbounded LZ76 parsing. Then the number of phrases of the exhaustive history of $x$, which is its Lempel-Ziv complexity, is at most $\frac{n}{(1 - \varepsilon_n)\log_k n}$, where $\varepsilon_n \to 0$ depends only on $n$ and $k$.

## Proof sketch

Combine the LZ78 phrase-count bound $c \le n/((1 - \varepsilon_n)\log_k n)$, which follows from the distinct-parsing inequality $m c \le n + 2k^m$, with the comparison LZ77 $\le$ LZ78, which holds because the window covers the input. Lempel and Ziv's bound, as quoted by Estevez-Rams et al., takes $\varepsilon_n = 2\,(1 + \log_k \log_k (kn))/\log_k n$; for the finitely many $n$ where this is not below $1$, any $\varepsilon_n < 1$ with $(1 - \varepsilon_n)\log_k n \le 1$ works, because the complexity is at most $n$.

The window hypothesis is needed. With window $1$, a phrase with its last symbol removed must be a run of the last symbol already written, so $(ab)^{n/2}$ needs $n$ phrases, which exceeds $n/((1 - \varepsilon_n)\log_k n)$ once $(1 - \varepsilon_n)\log_k n > 1$.

## Depends on

- [Reproducible phrases and Lempel-Ziv histories](lempel-ziv-histories.md)
- [The exhaustive history has the fewest phrases](exhaustive-history-optimality.md)

## Proof depends on

- [The LZ78 parse is an LZ77 history](lz78-parse-is-lz77-history.md)
- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Sources

- A. Lempel and J. Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1), 1976.
- E. Estevez-Rams, R. Lora Serrano, B. Aragón Fernández and I. Brito Reyes, "On the non-randomness of maximum Lempel Ziv complexity sequences of finite size", Chaos 23, 023118, 2013, Section II, equations (1) and (2).
- J. Ziv and A. Lempel, "Compression of Individual Sequences via Variable-Rate Coding", IEEE Transactions on Information Theory 24(5), 1978.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
