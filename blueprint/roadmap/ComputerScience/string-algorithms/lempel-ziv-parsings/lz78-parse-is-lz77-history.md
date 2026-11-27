# The LZ78 parse is an LZ77 history

In the LZ78 incremental parse every phrase is an earlier phrase (or the empty word) followed by one symbol, and an earlier phrase is a copy of text already written. Hence when the window covers the input, the LZ78 parse of $x$ is a history of $x$, and the number of LZ77 phrases of $x$ (and its Lempel-Ziv complexity) is at most the number of LZ78 phrases.

## Depends on

- [Reproducible phrases and Lempel-Ziv histories](lempel-ziv-histories.md)
- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Proof depends on

- [The exhaustive history has the fewest phrases](exhaustive-history-optimality.md)

## Sources

- J. Ziv and A. Lempel, "Compression of Individual Sequences via Variable-Rate Coding", IEEE Transactions on Information Theory 24(5), 1978.
- A. Lempel and J. Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1), 1976.
