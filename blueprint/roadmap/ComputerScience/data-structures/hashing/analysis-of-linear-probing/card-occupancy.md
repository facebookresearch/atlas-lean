# Linear probing places every item while the table has room

If a hash sequence has at most $N$ items, linear probing in a cyclic table of $N$ cells places
each item in its own cell: the [set of occupied cells](occupancy.md) has exactly as many elements
as there are items.

## Informally uses

- [An insertion into a table that is not full lands on an empty cell](insert-cell-not-mem.md):
  each insertion adds a new cell.
