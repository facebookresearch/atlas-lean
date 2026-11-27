# Balanced Ryser counterexamples at prime orders

There is $q_0$ such that for every prime $q\ge q_0$ there is a family of edges on $(q+1)$ parts each of size $q+1$. More precisely an edge is a choice function picking one labelled vertex from each part. The edge family is finite and nonempty, any two edges agree in at least one coordinate, and every labelled vertex in every part occurs in some edge. The smallest size of a set of vertices meeting every edge is exactly $q+1$.

## Depends on

- Partite choice-function model, nonisolation, pairwise intersection and minimum vertex cover.

## Proof outline

Construct the finite edge set, prove intersection and that all $q+1$ labels at every coordinate occur, and prove any cover contains at least $q+1$ vertices. Connect to the finite uniform-hypergraph API without dropping balancing or quantified prime threshold.

- Balanced prime-order construction with whole-part covering and exclusion of every smaller cover.

## Sources

- [Comparator statement: `OAI.Balanced.main_result`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BalancedRyser.lean#L39-L41)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/162.md)
