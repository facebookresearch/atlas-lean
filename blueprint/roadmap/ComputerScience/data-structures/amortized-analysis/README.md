# Amortized analysis

Amortization averages the running times of the operations of a sequence over the sequence: the
amortized time of an operation is its actual time plus the change it causes in a potential
function of the data structure, and the total actual time of a sequence is its total amortized
time plus the net decrease of the potential (Tarjan, *Amortized computational complexity*, SIAM
J. Algebraic Discrete Methods 6(2) (1985), §2). The statements here are generic in the
configurations, the cost model and the ordered group of values; the data-structure pages instantiate them.

- [Amortized cost of an operation](amortized-cost.md)
- [Potential method: telescoping identity](sum-cost-eq.md)
- [Potential method: amortized costs bound actual costs](sum-cost-le-sum-amortized-cost.md)
- [Potential method with a nonnegative potential that starts at zero](sum-cost-le-sum-amortized-cost-of-nonneg.md)
- [Potential method with per-operation amortized bounds](sum-cost-le-of-amortized-cost-le.md)

## Related topics

- [Two-list queue](../linear-structures/two-list-queue/README.md): potential equal to the
  length of the enqueue list.
- [Dynamic table](../linear-structures/dynamic-table/README.md): potential $2n - m$ for table
  doubling.
- [Binary counter](../linear-structures/binary-counter/README.md): potential equal to the number
  of one bits.
- [Stack with multipop](../linear-structures/stack-with-multipop/README.md): Tarjan's stack
  example, potential equal to the stack size.
- [Splay tree](../search-trees/splay-tree/README.md): the sum-of-logs potential and the access
  lemma, combined through the per-operation form of the potential method.
- [Disjoint-set data structure](../disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/README.md):
  union by rank with path compression, whose inverse-Ackermann bound is an amortized one.
- [List update problem](../../online-algorithms/list-update-problem/README.md): move-to-front,
  analysed with the inversion potential.

- [Amortized-analysis examples (1)](amortized-analysis-examples-1/README.md)

- [Amortized-analysis examples (2)](amortized-analysis-examples-2/README.md)

- [Logarithm lemmas](logarithm-lemmas/README.md)

- [The generic amortized framework](the-generic-amortized-framework/README.md)

- [The unary (sequence) amortized framework](the-unary-sequence-amortized-framework/README.md)
