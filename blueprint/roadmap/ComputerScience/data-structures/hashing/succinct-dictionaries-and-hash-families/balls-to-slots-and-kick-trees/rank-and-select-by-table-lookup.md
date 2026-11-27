# Rank and select on small bit vectors by table lookup

For a bit vector $x = x_0 x_1 \cdots x_{B-1} \in \{0,1\}^B$ (positions indexed from $0$), $\mathrm{rank}_1(x, i)$ for $0 \le i \le B$ is the number of ones among $x_0, \dots, x_{i-1}$, and for $j \ge 1$, $\mathrm{select}_1(x, j)$ is the position of the $j$-th one (undefined if $x$ has fewer than $j$ ones); $\mathrm{rank}_0, \mathrm{select}_0$ are defined symmetrically. These satisfy $\mathrm{rank}_0(x,i) = i - \mathrm{rank}_1(x,i)$, $\mathrm{rank}_1(x, \mathrm{select}_1(x, j)) = j - 1$ whenever the select is defined, and $\mathrm{select}_1(x,j)$ is defined iff $1 \le j \le \mathrm{rank}_1(x, B)$. On the word RAM with a structure of size parameter $n$, each operation on vectors with $B < (\log_2 n)/2$ is a function of the vector $x$ and an index in $[0, B]$, so it is answered in $O(1)$ time from a precomputed lookup table indexed by both, with $2^B (B + 1) < \sqrt{n}\,((\log_2 n)/2 + 1) = O(\sqrt{n} \log n)$ entries of $O(\log \log n)$ bits ($\tilde O(\sqrt{n})$ bits, shared by all instances); for $B = O(\log n)$, split $x$ into $O(1)$ such pieces and combine the per-piece answers in $O(1)$ time.

## Depends on

- [Succinct rank and select](../../../range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 4.1, lookup-table technique).
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
