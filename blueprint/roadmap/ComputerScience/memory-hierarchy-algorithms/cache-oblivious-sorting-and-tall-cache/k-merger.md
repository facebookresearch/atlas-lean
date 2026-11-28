# The k-merger (funnel)

A *$k$-merger* is a cache-oblivious data structure that merges $k$ sorted input streams and, in one invocation, outputs the next $k^3$ elements of the merged order. We take $k = 2^{2^j}$ for an integer $j \ge 0$, so that for $j \ge 1$ the number $\sqrt{k} = 2^{2^{j-1}}$ is again of this form and every count below is an integer. For $k = 2$ it is a binary merger. For $k \ge 4$ it consists of $\sqrt{k}$ *left* $\sqrt{k}$-mergers, each reading from $\sqrt{k}$ of the inputs, one *right* $\sqrt{k}$-merger, and $\sqrt{k}$ intermediate buffers of capacity $2k^{3/2}$ connecting them; it is laid out recursively in contiguous memory, with each sub-merger and buffer stored contiguously. An invocation calls the right merger $k^{3/2}$ times; before each call it refills every buffer holding fewer than $k^{3/2}$ elements by invoking the corresponding left merger once, which outputs $k^{3/2}$ elements.

## Depends on

- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
- Harald Prokop, "Cache-Oblivious Algorithms", Master's thesis, Massachusetts Institute of Technology (1999).
