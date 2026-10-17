---
article_id: af_31df568a971aabb076658f05
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.Knapsack.solve_correct
---

# Solve correct

The returned set is feasible, its reported value is its value sum, and it is globally
optimal among all feasible subsets of the input indices.

## Depends on

- [Feasible](feasible.md)
- [Item](item.md)
- [Result](result.md)
- [Solve](solve.md)
- [Total Value](total-value.md)

## Proof depends on

- [Total Weight](total-weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack](../../../../../../sources/v2/CSLibExt.md)
