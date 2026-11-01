---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Scheduling.lpt_step_le
---

# Lpt step le

The LPT step: when the jobs are placed in nonincreasing order, each placement of a job `p`
creates a load `L` with `3 * m * L ≤ (4 * m - 1) * M`.

## Depends on

- [Is Schedule Of](is-schedule-of.md)
- [Scan Inv](scan-inv.md)
- [Least Loaded](least-loaded.md)
- [Makespan](makespan.md)

## Proof depends on

- [Le makespan](le-makespan.md)
- [Sum le](sum-le.md)
- [Count P add count P le](count-p-add-count-p-le.md)
- [Mul least Loaded le](mul-least-loaded-le.md)
- [Two mul le of loads gt](two-mul-le-of-loads-gt.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.ListScheduling](../../../../../../sources/v2/CSLibExt.md)
