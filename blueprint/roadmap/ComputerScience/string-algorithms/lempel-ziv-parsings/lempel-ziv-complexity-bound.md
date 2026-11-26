# Lempel-Ziv complexity is O(n / log n)

Over an alphabet of size $k \ge 2$, the number of LZ77 phrases of a word of length $n$, and its Lempel-Ziv complexity, is at most $\frac{n}{(1 - \varepsilon_n)\log_k n}$ with $\varepsilon_n \to 0$.

## Proof sketch

Combine the LZ78 phrase-count bound $c \le n/((1 - \varepsilon_n)\log_k n)$, which follows from the distinct-parsing inequality $m c \le n + 2k^m$, with the comparison LZ77 $\le$ LZ78.

## Depends on

- [Reproducible phrases and Lempel-Ziv histories](lempel-ziv-histories.md)
- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Proof depends on

- [The LZ78 parse is an LZ77 history](lz78-parse-is-lz77-history.md)
- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Sources

- A. Lempel and J. Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1), 1976.
- J. Ziv and A. Lempel, "Compression of Individual Sequences via Variable-Rate Coding", IEEE Transactions on Information Theory 24(5), 1978.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
