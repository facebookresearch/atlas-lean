# Occupied cells after a hash sequence

For a hash sequence $a_1, \dots, a_k$ with values in the cells $0, \dots, N - 1$ of a cyclic table,
this is the set of occupied cells after the items are entered in order by linear probing,
starting from the empty table: each item adds to the set the
[cell given by its hash address and the cells already occupied](insert-cell.md). Once all $N$
cells are occupied, further items leave the set unchanged.
