# Aggarwal–Vitter bound for external sorting

In the external-memory model with internal memory of $M$ records and blocks of $B$ records, sorting $N$ records by comparisons requires $\Theta\!\left(\frac{N}{B}\log_{M/B}\frac{N}{B}\right)$ I/Os in the worst case (for $M \ge 2B$), and this bound is achieved by $(M/B)$-way merge sort.

## Proof sketch

The upper bound merges $\Theta(M/B)$ sorted runs at a time, so each of the $O(\log_{M/B}(N/B))$ merge passes scans the data in $O(N/B)$ I/Os. For the lower bound, an I/O that reads a block into a memory holding $M$ records can increase the number of consistent total orders compatible with the comparisons by a factor of at most $\binom{M}{B} B!$ for the first read of a block and $\binom{M}{B}$ afterwards; comparing with $N!$ orderings gives the bound.

## Depends on

- [The external-memory model](../external-memory-algorithms/the-external-memory-model.md)
- [I/O complexity of permuting](../external-memory-algorithms/i-o-complexity-of-permuting.md)
- [A binary tree with n! leaves has height at least log n!](../../sorting-and-searching/lower-bound-for-comparison-sorting/factorial-le-two-pow-height.md)

## Proof depends on

- [The external-memory model](../external-memory-algorithms/the-external-memory-model.md)
- [I/O complexity of permuting](../external-memory-algorithms/i-o-complexity-of-permuting.md)
- [A binary tree with n! leaves has height at least log n!](../../sorting-and-searching/lower-bound-for-comparison-sorting/factorial-le-two-pow-height.md)

## Sources

- Alok Aggarwal, Jeffrey Scott Vitter, "The Input/Output Complexity of Sorting and Related Problems", Communications of the ACM 31(9) (1988).
