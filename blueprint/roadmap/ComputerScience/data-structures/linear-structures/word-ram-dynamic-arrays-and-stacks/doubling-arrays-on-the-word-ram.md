# Doubling arrays on the Word RAM

A fixed word-RAM routine for appending to an array that doubles its capacity when full (allocating a zeroed block of twice the capacity and copying, in $O(c)$ instructions for capacity $c$), together with a constant-time indexed read, implements a growable array such that appending $m$ words to an initialized empty array takes $O(m)$ instructions in total and allocates at most $4m$ words (none when $m = 0$) (old blocks are retained, not reclaimed). Each append has amortized cost $O(1)$ instructions with respect to a potential proportional to $2 \cdot \mathrm{length} - \mathrm{capacity}$.

## Proof sketch

The doubling sizes form a geometric series, so the total copying work and allocated space are bounded by a constant times the final length. The potential pays for each copy: just before doubling it equals the capacity, and right after doubling it is zero.

## Depends on

- [Dynamic table](../dynamic-table/table.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Word-RAM implementation certificate with potential-amortized running time](../../data-structure-interfaces-and-refinement/word-ram-implementation-certificate.md)

## Proof depends on

- [Amortized cost of dynamic-table insertion](../dynamic-table/table-insert-amortized.md)
- [Potential method: amortized costs bound actual costs](../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
