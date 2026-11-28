# Tight cell-probe bounds for succinct Boolean matrix-vector multiplication

There is a systematic structure for Boolean matrix-vector multiplication that stores $O(n^{3/2}(\sqrt{w} + \lg n/\sqrt{w}))$ extra bits and, for every $v$, computes $Mv$ with probability at least $1 - 1/n$ by probing $O(n^{3/2}\sqrt{w}\lg n)$ cells, that is $\tilde{O}(n^{3/2})$ bits and probes for $w = \Theta(\lg n)$ (Theorem 1.1, with the probe count that Lemma 3.2 proves for its Algorithm 2, which samples $2\sqrt{nw}\lg n$ entries per row; the theorem's statement writes $\sqrt{w \lg n}$ in place of $\sqrt{w}\lg n$). Conversely, if every $M$ has an $r$-bit side structure and a randomized query algorithm that computes $Mv$ with probability at least $1 - 1/n$ while probing at most $t$ entries of $M$, then $t \cdot r = \Omega(n^3)$ for $n \le r \le n^2/4$, and $t = \Omega(n^2)$ for $r < n$ (Theorem 1.2). The lower bounds hold in the cell-probe model and so also for word-RAM structures.

## Proof sketch

For the upper bound, preprocessing greedily lists at most $n^{1/2}\sqrt{w}$ rectangles $I \times J$, each with at least $n^{3/2}/\sqrt{w}$ entries not yet covered and at most a $1/\sqrt{nw}$ fraction of ones per row among them, and stores the ones inside covered entries explicitly. A query with column set $J$ first settles rows through the stored ones, then samples $O(\sqrt{nw}\lg n)$ uncovered entries in each remaining row, and finally reads all remaining uncovered entries, of which there are few with high probability. For the lower bound, take $M$ uniformly from the matrices whose rows split into $r/n$ blocks of $n^2/r$ entries with exactly one $1$ per block, so $H(M) = r \lg(n^2/r)$. The answers to a fixed family of $4r/n$ queries carry much information about $M$, and the side structure together with a short encoding of the entries those queries probe (at most $4tr/n$ of them, of which the encoding records only the positions of the ones) lets a decoder replay the queries; comparing the encoding length with the entropy gives $tr = \Omega(n^3)$.

## Depends on

- [Succinct Boolean matrix-vector multiplication](succinct-boolean-matvec-problem.md)

## Sources

- Diptarka Chakraborty, Lior Kamma, Kasper Green Larsen, "Tight Cell Probe Bounds for Succinct Boolean Matrix-Vector Multiplication", STOC (2018), arXiv:1711.04467.
