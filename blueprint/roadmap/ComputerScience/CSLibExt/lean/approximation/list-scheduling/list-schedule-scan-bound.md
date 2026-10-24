---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Scheduling.listScheduleScan_bound
---

# List Schedule Scan bound

A bound `a * C ≤ b * M` holds for the final schedule if it holds initially and every
placement creates a load within it.

## Depends on

- [Scan Inv](scan-inv.md)
- [Least Loaded](least-loaded.md)
- [List Schedule Scan](list-schedule-scan.md)
- [Makespan](makespan.md)

## Proof depends on

- [Is Schedule Of](is-schedule-of.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.ListScheduling](../../../../../../sources/v2/CSLibExt.md)
