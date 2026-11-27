/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.FoundNewRunSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

private def foundNewRunUnpoweredOlder : PendingRun :=
  { base := 0, len := 1, power := none }

private def foundNewRunUnpoweredNewest : PendingRun :=
  { base := 1, len := 1, power := none }

private def foundNewRunUnpoweredRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private theorem foundNewRunUnpoweredRegressionState_not_powered :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState := by
  intro hpowered
  rcases hpowered with hempty |
      ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp [foundNewRunUnpoweredRegressionState] at hempty
  · have hsplit' :
        [foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest] =
          olderRuns ++ [top] := by
      simpa [foundNewRunUnpoweredRegressionState] using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    rcases honly with ⟨storedPower, hsome, _hrange⟩
    have hsomeOlder : foundNewRunUnpoweredOlder.power = some storedPower := by
      simpa [hsplit'.1] using hsome
    simp [foundNewRunUnpoweredOlder] at hsomeOlder

/-- Anti-vacuity regression for the invalid `preceding.power = none` arm.  A
concrete two-run state violates `PoweredPrefix`; the attempted second-last read
is still visible, after which the collapse evaluator returns `none` without a
fuel marker or push. -/
theorem foundNewRunLoopTraced_unpowered_preceding_failure :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).result =
        none ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.accesses =
        [{ kind := .read
           region := .pendingRuns
           index := 0
           extent := 2 }] ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted =
        false ∧
      (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.pushDepths =
        [] := by
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

/-- End-to-end form of the same anti-vacuity regression.  The outer evaluator
passes its source-domain guard, records the current-top read, enters the
collapse loop, records the uninitialized preceding run, and then fails. -/
theorem foundNewRunTraced_unpowered_prefix_failure :
    ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).result = none ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.accesses =
        [{ kind := .read
           region := .pendingRuns
           index := 1
           extent := 2 },
         { kind := .read
           region := .pendingRuns
           index := 0
           extent := 2 }] ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted =
        false ∧
      (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.pushDepths =
        [] := by
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

end CPythonListsort
