---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Scheduling.listSchedule_isScheduleOf
---

# List Schedule is Schedule Of

Graham (1969): LPT has makespan `C` with `3 * m * C ≤ (4 * m - 1) * M` for the makespan `M`
of every schedule `τ` of the same jobs, i.e. `C ≤ (4/3 - 1/(3m)) M`. -/
theorem lpt_approx [NeZero m] (ps : List ℕ) (τ : Fin m → List ℕ) (hτ : IsScheduleOf τ ps) :
    3 * m * makespan (lpt m ps).ret ≤ (4 * m - 1) * makespan τ := by
  set sorted := ((mergeSort (ps.map OrderDual.toDual)).ret).map OrderDual.ofDual
  have hperm : sorted.Perm ps := by
    have := (mergeSort_perm (ps.map OrderDual.toDual)).map OrderDual.ofDual
    simpa [sorted, List.map_map] using this
  have hsorted : sorted.Pairwise (· ≥ ·) := by
    have := mergeSort_sorted (ps.map OrderDual.toDual)
    exact List.Pairwise.map _ (fun a b h => h) this
  have hτ' : IsScheduleOf τ sorted := hτ.perm hperm.symm
  simp only [lpt, ret_bind]
  apply listScheduleScan_bound scanInv_init sorted (by simp)
  intro P' p rest' loads' σ' heq hinv
  exact lpt_step_le (by simpa using heq) hsorted hinv τ hτ'

/-! ## Validity and cost

## Depends on

- [Is Schedule Of](is-schedule-of.md)
- [List Schedule](list-schedule.md)

## Proof depends on

- [Scan Inv](scan-inv.md)
- [Is Schedule Of nil](is-schedule-of-nil.md)
- [Least Loaded](least-loaded.md)
- [List Schedule Scan](list-schedule-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.ListScheduling](../../../../../../sources/v2/CSLibExt.md)
