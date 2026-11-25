# Constant-time OR and maximum on a common CRCW PRAM

On a common CRCW PRAM, where processors writing to the same cell in the same step must write the same value, the OR of $n$ bits is computed in $O(1)$ steps by $n$ processors: every processor holding a $1$ writes $1$ to a cell initialized to $0$. The maximum of $n$ values $x_1, \dots, x_n$ is computed in $O(1)$ steps by $n^2$ processors: processor $(i, j)$ marks index $i$ as not maximal if $x_i < x_j$, and every processor $i$ whose index is unmarked writes the value $x_i$ to the output cell. All unmarked indices hold the maximal value, so the concurrent writes agree. To output an index of a maximum instead, break ties by index: processor $(i, j)$ also marks $i$ when $x_i = x_j$ and $i > j$, which leaves exactly one unmarked index.

## Expansion

This page becomes ready once:

- PRAM model (statement prerequisite; formal statement exists, page pending)
- The PRAM conventions (n ≥ 1, zero-initialized shared cells, synchronous steps) must be fixed by the PRAM model page

## Sources

- J. JáJá, *An Introduction to Parallel Algorithms*, Addison-Wesley, 1992
- D. R. Karger, *6.854 Advanced Algorithms*, lecture notes on parallel algorithms, MIT
