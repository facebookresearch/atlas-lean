---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Scheduling.isScheduleOf_nil
---

# Is Schedule Of nil

LPT: sort the jobs into nonincreasing order with CSLib's `mergeSort`, then list-schedule. -/
def lpt (m : ℕ) [NeZero m] (ps : List ℕ) : TimeM ℕ (Fin m → List ℕ) := do
  let sorted ← mergeSort (ps.map OrderDual.toDual)
  listSchedule m (sorted.map OrderDual.ofDual)

/-! ## Schedules

## Depends on

- [Is Schedule Of](is-schedule-of.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.ListScheduling](../../../../../../sources/v2/CSLibExt.md)
