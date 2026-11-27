# Rank and select on small bit vectors by table lookup

For a bit vector $x \in \{0,1\}^B$ with $B = O(\log n)$ small enough that tables indexed by $x$ have $o(n)$ entries, $\mathrm{rank}_1(x, i)$ is the number of ones among the first $i$ bits, $\mathrm{select}_1(x, j)$ is the position of the $j$-th one (undefined if $x$ has fewer than $j$ ones), and $\mathrm{rank}_0, \mathrm{select}_0$ are defined symmetrically. Precomputed lookup tables answer each operation in $O(1)$ time; they satisfy $\mathrm{rank}_0(x,i) = i - \mathrm{rank}_1(x,i)$, $\mathrm{rank}_1(x, \mathrm{select}_1(x, j)) = j - 1$ whenever the select is defined, and $\mathrm{select}_1(x,j)$ is defined iff $j \le \mathrm{rank}_1(x, B)$.

## Depends on

- [Succinct rank and select](../../../range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
