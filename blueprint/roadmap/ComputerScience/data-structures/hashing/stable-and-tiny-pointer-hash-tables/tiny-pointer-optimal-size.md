# Optimal sizes of tiny pointers

For dereference tables with load factor $1 - \delta$ on $n$ slots and constant-time operations, the optimal tiny-pointer size is $\Theta(\log \log \log n + \log \delta^{-1})$ bits in the fixed-size case, and $\Theta(1 + \log \delta^{-1})$ expected bits in the variable-size case; both bounds are achieved by explicit constructions with failure probability that can be made small, and are tight up to constant factors.

## Proof sketch

For the variable-size case, a key hashes to a sequence of geometrically growing candidate regions and the pointer records which region and offset it ended in, costing $O(1 + \log\delta^{-1})$ bits in expectation by a balls-into-bins tail bound. For fixed-size pointers, a two-level scheme first assigns each key to a bucket via load-balancing with $O(\log\log\log n)$ bits of choice information and then indexes within a bucket of size $\mathrm{poly}(\delta^{-1})$. Matching lower bounds come from counting how many keys can share the slots addressable by short pointers.

## Depends on

- [Tiny pointers and dereference tables](tiny-pointer.md)

## Proof depends on

- [Maximum load of balls into bins](../../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Tiny Pointers", SODA (2023); ACM Transactions on Algorithms (2025), arXiv:2111.12800.
