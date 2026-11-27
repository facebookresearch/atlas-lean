/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.TopLevelErasure

/-!
# Raw-domain erasure for `merge_force_collapse`

These structural lemmas have no layout, liveness, comparator-law, or
successful-execution premises.  They use only the full-domain erasure bridge
for each delegated `merge_at` call.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Structural erasure for the recursive final-collapse loop, parameterized
only by the erasure bridge for each delegated `merge_at` call. -/
theorem erase_mergeForceCollapseLoopTraced_of_mergeAt
    (hMergeAt : ∀ (state : MergeState κ ν) (i : Nat),
      (mergeAtTraced? state i).erase = mergeAt? state i)
    (fuel : Nat) (state : MergeState κ ν) :
    (mergeForceCollapseLoopTraced? fuel state).erase =
      mergeForceCollapseLoop? fuel state := by
  induction fuel generalizing state with
  | zero =>
      simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
      by_cases hdone : state.pending.size ≤ 1
      · rw [ite_eq_left hdone, ite_eq_left hdone]
        rfl
      · rw [ite_eq_right hdone, ite_eq_right hdone]
        simp [TraceResult.erase_markFuelExhausted]
        rfl
  | succ fuel ih =>
      simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
      by_cases hmany : 1 < state.pending.size
      · rw [ite_eq_left hmany, ite_eq_left hmany, TraceResult.erase_bind,
          erase_forceCollapseIndexTraced]
        cases hindex : forceCollapseIndex? state with
        | none => simp
        | some i =>
            simp only [Option.bind_some, TraceResult.erase_bind,
              hMergeAt]
            cases hmerged : mergeAt? state i with
            | none => simp
            | some merged =>
                simp only [Option.bind_some]
                by_cases hContinue :
                    merged.returnCode = 0 ∧ !merged.fuelExhausted
                · rw [ite_eq_left hContinue, ite_eq_left hContinue]
                  exact ih merged.state
                · rw [ite_eq_right hContinue, ite_eq_right hContinue]
                  rfl
      · rw [ite_eq_right hmany, ite_eq_right hmany]
        rfl

/-- Unconditional raw-domain erasure for the complete traced
`merge_force_collapse` evaluator. -/
theorem erase_mergeForceCollapseTraced (state : MergeState κ ν) :
    (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state := by
  exact erase_mergeForceCollapseLoopTraced_of_mergeAt erase_mergeAtTraced
    state.pending.size state

end CPythonListsort
