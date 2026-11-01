---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.matroidGreedyScan_append
---

# Matroid Greedy Scan append

One oracle query per element. -/
@[simp]
theorem matroidGreedy_time (indep : Finset α → Bool) (es : List α) :
    (matroidGreedy indep es).time = es.length :=
  matroidGreedyScan_time indep ∅ es

/-! ## The scan invariant

## Depends on

- [Matroid Greedy Scan](matroid-greedy-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy](../../../../../../sources/v2/CSLibExt.md)
