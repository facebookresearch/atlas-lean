---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Scheduling.listSchedule_approx
---

# List Schedule approx

Graham (1966): list scheduling in any order has makespan `C` with
`m * C ≤ (2 * m - 1) * M` for the makespan `M` of every schedule `τ` of the same jobs.

## Depends on

- [Is Schedule Of](is-schedule-of.md)
- [List Schedule](list-schedule.md)
- [Makespan](makespan.md)

## Proof depends on

- [Le makespan](le-makespan.md)
- [Sum le](sum-le.md)
- [Scan Inv](scan-inv.md)
- [Is Schedule Of nil](is-schedule-of-nil.md)
- [Least Loaded](least-loaded.md)
- [List Schedule Scan bound](list-schedule-scan-bound.md)
- [Mul least Loaded le](mul-least-loaded-le.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.ListScheduling](../../../../../../sources/v2/CSLibExt.md)
