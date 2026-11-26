# Stable hash tables

A dynamic hash table storing at most $n$ keys of a universe $U$ in an array is *stable* if the array position of every stored key changes only during resize operations: between resizes, insertions and deletions of other keys never move it. Stability allows external pointers to stored keys to remain valid. The table's *load factor* is the number of stored keys divided by the number of slots.

## Depends on

- [Open-addressing hash table](../open-addressing/open-addressing.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6) (2023), arXiv:2109.04548.
