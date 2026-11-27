# Correctness and cost of bucket elimination

For any elimination order covering all variables, bucket elimination returns the contraction $\sum_{\sigma} \prod_{\phi} \phi(\sigma)$ of the factor network (in particular the number of solutions of a CSP, or the partition function of a weighted CSP). If every variable lies in the scope of some initial factor, the number of live factors never increases along the order, and the total number of semiring operations is at most the sum over buckets of $d^{\,|\text{joint scope}|} \cdot |\text{bucket}|$ plus $\max(|F| - 1, 0)$ for the final product of the remaining constant factors, hence at most $\ell \cdot |F| \cdot d^{\,w^* + 1} + \max(|F| - 1, 0)$ for induced width $w^*$. On the word RAM with unit-cost multiplication, the same bounds hold for instructions up to a constant factor, at word sizes that hold all intermediate entries.

## Proof sketch

Distributivity: the sum over $x_i$ commutes with every factor not containing $x_i$, so eliminating $x_i$ preserves the contraction. Each entry of a bucket's new factor costs $d(|\text{bucket}| - 1)$ multiplications and $d - 1$ additions, so the bucket costs at most $d^{\,|\text{joint scope}|} \cdot |\text{bucket}|$. A factor containing a variable either lies in that variable's bucket or was absorbed into a factor that still contains it, so no bucket is empty and each bucket replaces at least one live factor by one; at most $|F|$ constant factors therefore remain, and multiplying them costs at most $|F| - 1$ operations. That term is needed: one variable with $d = 2$, one factor on it and $100$ factors with empty scope cost $1 + 100$ operations.

## Depends on

- [Bucket elimination over explicit factor tables](bucket-elimination-over-factor-tables.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Variable elimination computes the partition function](../../machine-learning/probabilistic-graphical-models/variable-elimination-and-belief-propagation/partition-eq.md)

## Sources

- R. Dechter, "Bucket Elimination: A Unifying Framework for Reasoning", Artificial Intelligence 113(1-2), 1999.
