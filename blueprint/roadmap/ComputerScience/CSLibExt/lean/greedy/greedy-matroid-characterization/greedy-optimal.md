---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.GreedyOptimal
---

# Greedy Optimal

The greedy algorithm is optimal for `indep` on the finite type `α`: for every weight function
and every listing of all elements in nonincreasing weight order, its result weighs at least as
much as every independent set. (`Finite α` keeps this from holding vacuously: on an infinite type
no list covers every element; the instance is a hypothesis of the definition, not used in its
body, hence the `nolint`.)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Matroid Greedy](../matroid-greedy/matroid-greedy.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.GreedyMatroidCharacterization](../../../../../../sources/v2/CSLibExt.md)
