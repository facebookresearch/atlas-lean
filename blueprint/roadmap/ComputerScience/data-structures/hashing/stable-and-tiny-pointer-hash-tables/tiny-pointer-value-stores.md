# Space-efficient value stores from tiny pointers

Suppose a user stores, alongside each of $n$ keys, a tiny pointer of expected size $O(1)$ bits. Then a data structure storing a $v$-bit value for each of the $n$ keys with constant-factor time overhead for modifications and queries can be implemented in $n v + O(n \log^{(r)} n)$ bits of space, for any constant $r \ge 1$, where $\log^{(r)}$ denotes the $r$-th iterated logarithm.

## Proof sketch

Allocate the values in a dereference table at load factor $1 - \delta$ with $\delta = 1/\log^{(r)} n$, so the wasted space is $O(\delta n v)$ plus the metadata of the construction; recursive application of the fixed-size tiny-pointer construction to its own metadata reduces the overhead per level by one iterated logarithm.

## Depends on

- [Tiny pointers and dereference tables](tiny-pointer.md)

## Proof depends on

- [Optimal sizes of tiny pointers](tiny-pointer-optimal-size.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Tiny Pointers", SODA (2023); ACM Transactions on Algorithms (2025), arXiv:2111.12800.
