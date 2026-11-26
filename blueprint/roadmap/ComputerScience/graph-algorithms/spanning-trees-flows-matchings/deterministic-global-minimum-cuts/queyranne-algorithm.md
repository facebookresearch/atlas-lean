# Queyranne's algorithm minimizes symmetric submodular functions

Let $f$ be a symmetric submodular function on a finite set $V$ with $|V| \ge 2$, with values in a linearly ordered abelian monoid with cancellation. **Queyranne's algorithm** repeatedly finds a pendent pair $(s, t)$ by an MA ordering of the current elements, records $f$ of the merged class of $t$, and merges $t$ into $s$; it returns a nontrivial subset $S \subsetneq V$, $S \ne \emptyset$, minimizing $f$ over all nontrivial subsets. Examples include global minimum cuts of graphs and of hypergraphs.

## Proof sketch

Same induction as Stoer-Wagner, with submodularity and symmetry replacing the graph-specific counting in the pendent pair lemma.

## Depends on

- [Maximum adjacency orderings](maximum-adjacency-ordering.md)
- [Submodular set function](../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Proof depends on

- [The last vertex of an MA ordering is a minimum cut for the pendent pair](pendent-pair-lemma.md)

## Sources

- M. Queyranne, "Minimizing Symmetric Submodular Functions", Mathematical Programming 82, 1998.
