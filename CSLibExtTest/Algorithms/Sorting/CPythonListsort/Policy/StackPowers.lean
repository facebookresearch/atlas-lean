/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Policy.StackPowers

/-! # Pending-stack power invariant regressions -/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A singleton steady-state stack is valid regardless of its stale or
uninitialized stored power. -/
example (state : MergeState κ ν) (run : PendingRun) :
    PoweredPrefix { state with pending := #[run] } := by
  exact poweredPrefix_singleton state run

/-- Two unpowered runs are invalid: only the unique newest run may lack a
power. -/
example (state : MergeState κ ν) (older newest : PendingRun)
    (holder : older.power = none) (_hnewest : newest.power = none) :
    ¬PoweredPrefix { state with pending := #[older, newest] } := by
  intro h
  rcases h with hempty | ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp at hempty
  · have hsplit' : [older, newest] = olderRuns ++ [top] := by simpa using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    rcases honly with ⟨power, hsome, _⟩
    have hsomeOlder : older.power = some power := by
      simpa [hsplit'.1] using hsome
    rw [holder] at hsomeOlder
    simp at hsomeOlder

private def mislabeledOlder : PendingRun :=
  { base := 0, len := 1, power := some 2 }

private def unlabeledNewest : PendingRun :=
  { base := 1, len := 1, power := none }

/-- On the fabricated two-run geometry, the transcribed source computes
boundary power `1`, not the stored label `2`.  This uses ordinary kernel
reduction rather than an external evaluator. -/
private theorem mislabeledBoundary_true_power :
    pendingBoundaryPower 0 (3 : PySSize) mislabeledOlder unlabeledNewest = 1 := by
  decide

/-- Regression: range and shape alone are insufficient.  The formerly
admitted fabricated stack is rejected because its first stored label is `2`
while `powerloop 0 1 1 3` returns `1`. -/
theorem fabricatedTwoRunStack_not_powered (state : MergeState κ ν) :
    ¬PoweredPrefix
      { state with
        listlen := 3
        basekeys := 0
        pending :=
          #[{ base := 0, len := 1, power := some 2 },
            { base := 1, len := 1, power := none }] } := by
  change ¬PoweredPrefix
    { state with
      listlen := 3
      basekeys := 0
      pending := #[mislabeledOlder, unlabeledNewest] }
  intro h
  have hexact := h.exact_boundary_powers
  have hlabel := hexact.head
  rw [mislabeledBoundary_true_power] at hlabel
  simp [mislabeledOlder] at hlabel

end CPythonListsort
