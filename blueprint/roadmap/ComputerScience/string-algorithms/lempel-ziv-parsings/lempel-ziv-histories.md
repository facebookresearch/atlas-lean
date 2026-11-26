# Reproducible phrases and Lempel-Ziv histories

Let $h$ be a word already written and $W \ge 1$ a window size. A word $u$ is **reproducible** from $h$ within window $W$ if $u$ can be written by copying symbols one at a time from $d$ positions back, for a fixed $1 \le d \le \min(W, |h|)$; the copy may overlap $u$ itself (so $aaaa$ is reproducible from $a$ with $d = 1$), and the empty word is reproducible from every $h$. A **history** of a word $x$ is a factorization $x = u_1 u_2 \cdots u_c$ into nonempty phrases such that each $u_i$ with its last symbol removed is reproducible from $u_1 \cdots u_{i-1}$. The **exhaustive history** (LZ76 parsing, LZ77 with an unbounded window) takes each phrase as long as possible.

## Depends on

- [LZ78 incremental parsing and phrase-count bound](../../../InformationTheory/source-coding/lz78-incremental-parsing-and-phrase-count-bound.md)

## Sources

- A. Lempel and J. Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1), 1976.
- J. Ziv and A. Lempel, "A Universal Algorithm for Sequential Data Compression", IEEE Transactions on Information Theory 23(3), 1977.
