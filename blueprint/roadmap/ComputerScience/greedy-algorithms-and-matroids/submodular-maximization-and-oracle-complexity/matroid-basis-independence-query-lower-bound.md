# Finding a matroid basis needs n independence queries

Every deterministic independence-oracle algorithm that finds a basis, or even only a maximum-cardinality independent subset, of every matroid on a list of $n$ distinct elements makes at least $n$ independence queries in the worst case. The greedy algorithm makes exactly $n$ queries, so the bound is tight with constant $1$.

## Proof sketch

Against the all-loops oracle, if some singleton $\{x\}$ is never queried, changing $x$ into a coloop changes no answer but makes the returned set (which avoids $x$) non-maximum.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Optimality of the matroid greedy algorithm](../matroid-greedy-algorithm/matroid-greedy-optimal.md)

## Sources

- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
