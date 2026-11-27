# A* with planning heuristics returns optimal plans

A STRIPS task in positive normal form with operator costs at least $1$ induces a deterministic search
problem whose states are the reachable atom sets, whose actions are the applicable operators and whose
step costs are the operator costs; plans correspond to solutions with the same cost. On this problem:

1. A* graph search without reopening, with $h_{\max}$, returns a cost-optimal plan whenever a plan
   exists, by the consistent-heuristic case of the A* graph theorem;
2. A* tree search, or A* graph search with reopening, with $h^{\mathrm{LM\text{-}cut}}$ returns a cost-optimal
   plan whenever a plan exists, by the admissible-heuristic case.

Both heuristics are $\infty$ on states from which the goal is not relaxed reachable; such states can be
pruned, since no plan passes through them. The bridge states only the encoding; costs, consistency and
reopening assumptions are those of the A* pages.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: STRIPS planning as search.

## Depends on

- [h_max and h_add](h-max-and-h-add.md)
- [LM-cut heuristic](lm-cut-heuristic.md)

## Proof depends on

- [A* graph search: consistency, monotone f and reopening](../a-search-algorithm/a-graph-search-consistency-monotone-f-and-reopening.md)
- [A* tree search is optimal under an admissible heuristic](../a-search-algorithm/a-tree-search-is-optimal-under-an-admissible-heuristic.md)

## Sources

- M. Helmert and C. Domshlak, *Landmarks, critical paths and abstractions: what's the difference anyway?*, ICAPS 2009, Preliminaries: optimal planning with A\* requires admissible heuristics. The bridge itself follows from the A\* theorems applied to the induced search problem. <https://ai.dmi.unibas.ch/_files/teaching/hs19/po/misc/helmert-domshlak-icaps2009.pdf>
