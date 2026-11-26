# Bucket elimination over explicit factor tables

A **factor** over a finite domain $[d]$ is a pair (scope $\subseteq V$, table assigning a value in a commutative semiring $R$ to every assignment of its scope). Given a list of factors and an elimination order $x_1, \dots, x_\ell$ of variables, **bucket elimination** processes $x_i$ by collecting the **bucket** of live factors whose scope contains $x_i$, replacing them by the single factor on the union of their scopes minus $x_i$ whose entries are $\sum_{a \in [d]} \prod_{\phi \in \text{bucket}} \phi(\cdot, x_i = a)$, and finally multiplying the remaining constant factors. The **intermediate scopes** are the joint scopes of the buckets; their maximum size is one more than the induced width of the order.

## Depends on

- [Adaptive consistency via bucket elimination](../../heuristic-search-and-planning/constraint-satisfaction-consistency-and-width/adaptive-consistency-via-bucket-elimination.md)
- [Variable elimination computes the partition function](../../machine-learning/probabilistic-graphical-models/variable-elimination-and-belief-propagation/partition-eq.md)

## Sources

- R. Dechter, "Bucket Elimination: A Unifying Framework for Reasoning", Artificial Intelligence 113(1-2), 1999.
