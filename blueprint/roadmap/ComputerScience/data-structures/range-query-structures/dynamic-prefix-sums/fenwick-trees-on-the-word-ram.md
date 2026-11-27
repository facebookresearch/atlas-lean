# Fenwick trees on the Word RAM

For every length $n$, a Fenwick tree stored in exactly $n$ words is realized by a word-RAM program that answers $\mathrm{sum}(\ell)$ and performs $\mathrm{add}(i, \delta)$ in $O(\log n)$ instructions each, using the bitwise lowest-set-bit identities, and that requires only that $b + n$ fits in a word for base address $b$ (the upward step compares $n - m < \mathrm{lowbit}(m)$ before forming $m + \mathrm{lowbit}(m)$). The tree for an initial list of length $n$ is built in place in $O(n)$ instructions.

## Proof sketch

A prefix query visits the indices obtained by repeatedly clearing the lowest set bit, and an update visits those obtained by repeatedly adding it; each sequence has at most $\lceil \log_2(n+1) \rceil$ terms and each step costs a constant number of instructions. In-place construction adds each cell to its immediate parent once, in increasing order.

## Depends on

- [Fenwick tree](../fenwick-tree/fenwick-tree.md)
- [Dynamic prefix sums problem](dynamic-prefix-sums.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Bitwise identities for the lowest set bit](bitwise-identities-for-the-lowest-set-bit.md)
- [Fenwick prefix queries and updates have logarithmically many probes](../fenwick-tree/fenwick-tree-operations-take-logarithmic-time.md)

## Sources

- P. M. Fenwick, "A New Data Structure for Cumulative Frequency Tables", Software: Practice and Experience 24(3), pp. 327-336, 1994.
