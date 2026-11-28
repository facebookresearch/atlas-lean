# Top-trading envy-cycle elimination gives EF1 for monotone chores

Let $n$ agents have monotone cost functions $c_i : 2^M \to \mathbb{R}_{\ge 0}$ on a finite set of chores ($S \subseteq T$ implies $c_i(S) \le c_i(T)$). Allocate chores one at a time; at each step give the next chore to an agent who envies nobody (a sink of the envy graph), and if no sink exists, resolve the cycles of the top-trading graph, in which each agent points to an agent whose bundle she likes most, by rotating bundles along a cycle. The resulting allocation is EF1 for chores: for all $i, j$ with $X_i \ne \emptyset$ there is $e \in X_i$ with $c_i(X_i \setminus \{e\}) \le c_i(X_j)$.

## Proof sketch

Ordinary envy-cycle elimination may fail for chores because rotating an arbitrary envy cycle can create new envy that is not removable by one chore. In the top-trading graph every agent receives her favourite bundle on the cycle, so after rotation she envies no bundle; hence some sink exists after resolving top-trading cycles, and giving the new chore to an envy-free agent keeps EF1 because her envy is removable by that last chore.

## Depends on

- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)
- [Envy cycle](../../../not-yet-classified/part-01/indivisible/is-envy-cycle.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](../efx-allocations-charity-and-counterexamples/envy-cycle-rotation-preserves-efx.md)

## Sources

- U. Bhaskar, A. R. Sricharan, R. Vaish, "On Approximate Envy-Freeness for Indivisible Chores and Mixed Resources", APPROX 2021, arXiv:2012.06788.
