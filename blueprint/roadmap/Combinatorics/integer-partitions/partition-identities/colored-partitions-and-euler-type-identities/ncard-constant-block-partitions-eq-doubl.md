# Constant-block partitions and double compositions

For $n \ge 0$, count the pairs
$(A, P)$ where $A$ is a multiset of $n$ positive integers whose distinct elements are exactly
$1, \dots, k$ for some $k \ge 0$, and $P$ is a partition of $A$ into constant blocks, that is,
a multiset of nonempty multisets, each with all its elements equal, whose sum is $A$. The number
of such pairs equals the number $d_c(n)$ of double compositions of $n$, that is, compositions of
$n$ in which each summand $m$ is colored by a partition of $m$:

$$d_c(n) = \sum_{(c_1, \dots, c_r)} p(c_1) \cdots p(c_r),$$

where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ and $p(m)$ is the number of
partitions of $m$.

## Sources

- Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type Identities*, INTEGERS 26 (2026), Article A20, Theorem 4 (`integers-2026-A20-thm-4`).
