# The LZ78 bit code and its length

Write the $i$-th LZ78 (pointer, symbol) pair, counting from $1$, with the pointer in $\{0, \dots, i - 1\}$ using $\lceil \log_2 i \rceil$ bits and the symbol using $\lceil \log_2 k \rceil$ bits under a fixed numbering of the alphabet (least significant bit first). Since widths depend only on positions, the code is uniquely decodable without separators for $k \ge 2$, and a word parsed into $c$ phrases is encoded with $\sum_{i=1}^{c}(\lceil \log_2 i \rceil + \lceil \log_2 k \rceil) \le c(\lceil \log_2 c \rceil + \lceil \log_2 k \rceil)$ bits; by the phrase-count bound this is $O(n \log k)$.

## Depends on

- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Sources

- J. Ziv and A. Lempel, "Compression of Individual Sequences via Variable-Rate Coding", IEEE Transactions on Information Theory 24(5), 1978.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
