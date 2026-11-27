# Correctness and cost of bucket elimination

For any elimination order covering all variables, bucket elimination returns the contraction $\sum_{\sigma} \prod_{\phi} \phi(\sigma)$ of the factor network (in particular the number of solutions of a CSP, or the partition function of a weighted CSP). If every variable lies in the scope of some initial factor, the number of live factors never increases along the order, and the total number of semiring operations is at most the sum over buckets of $d^{\,|\text{joint scope}|} \cdot |\text{bucket}|$, hence at most $\ell \cdot |F| \cdot d^{\,w^* + 1}$ for induced width $w^*$. On the word RAM with unit-cost multiplication, the same bound holds for instructions up to a constant factor, at word sizes that hold all intermediate entries.

## Proof sketch

Distributivity: the sum over $x_i$ commutes with every factor not containing $x_i$, so eliminating $x_i$ preserves the contraction.

## Depends on

- [Bucket elimination over explicit factor tables](bucket-elimination-over-factor-tables.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Variable elimination computes the partition function](../../machine-learning/probabilistic-graphical-models/variable-elimination-and-belief-propagation/partition-eq.md)

## Sources

- R. Dechter, "Bucket Elimination: A Unifying Framework for Reasoning", Artificial Intelligence 113(1-2), 1999.
