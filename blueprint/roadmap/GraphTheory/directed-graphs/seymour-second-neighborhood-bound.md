# Seymour's second out-neighborhood inequality

In every finite nonempty digraph with no loops and no oppositely oriented pair of arcs there is a vertex $v$ with at least as many second out-neighbors as first out-neighbors. The first set is $\{w:v\to w\}$; the second is $\{w\ne v:\ v\not\to w,\ \exists u\ (v\to u\to w)\}$. Each vertex counts once, not once per walk.

## Depends on

- Finite oriented loopless relation and exactly-two directed reachability.

## Proof outline

Separate the counterexample reduction and the matching/rank pruning estimates from the final contradiction. Include the sink case (both sets empty); never count first neighbors reached in two steps.

- Counterexample reduction to positive-growth instances, pruning, and extremal contradiction excluding strict subset growth.

## Sources

- [Comparator statement: `OAI.SeymourSecondNeighborhood.exists_goodVertex`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SeymourSecondNeighborhood.lean#L34-L37)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/173.md)
- [Proof assembly for the finite oriented-graph claim](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SecondNeighborhood/Main.lean)
