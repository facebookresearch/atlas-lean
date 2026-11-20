/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.TopLevelErasure

/-!
# Raw-domain erasure for `found_new_run`

These structural lemmas have no layout, liveness, comparator-law, or
successful-execution premises. They use only the full-domain erasure bridge
for each delegated `merge_at` call.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Structural erasure for the recursive PowerSort-policy loop, parameterized
only by the erasure bridge for each delegated `merge_at` call. -/
theorem erase_foundNewRunLoopTraced_of_mergeAt
    (hMergeAt : ∀ (state : MergeState κ ν) (i : Nat),
      (mergeAtTraced? state i).erase = mergeAt? state i) :
    ∀ (fuel : Nat) (state : MergeState κ ν) (power : Nat),
      (foundNewRunLoopTraced? fuel state power).erase =
        foundNewRunLoop? fuel state power := by
  intro fuel
  induction fuel with
  | zero =>
      intro state power
      simp [foundNewRunLoopTraced?, foundNewRunLoop?,
        TraceResult.erase_markFuelExhausted, foundNewRunOutOfFuel_eq]
      rfl
  | succ fuel ih =>
      intro state power
      simp only [foundNewRunLoopTraced?, foundNewRunLoop?]
      by_cases hmany : 1 < state.pending.size
      · rw [if_pos hmany, if_pos hmany, TraceResult.erase_bind,
          TraceResult.erase_pendingRunRead]
        have hnonnegative :
            0 ≤ Int.ofNat (state.pending.size - 2) := Int.natCast_nonneg _
        rw [if_pos hnonnegative]
        have htoi :
            (Int.ofNat (state.pending.size - 2)).toNat =
              state.pending.size - 2 := rfl
        rw [htoi]
        cases hpreceding : state.pending[state.pending.size - 2]? with
        | none => simp
        | some preceding =>
            simp only [Option.bind_some]
            cases hpower : preceding.power with
            | none => simp
            | some precedingPower =>
                simp only
                by_cases hcollapse : power < precedingPower
                · rw [if_pos hcollapse, if_pos hcollapse,
                    TraceResult.erase_bind, hMergeAt]
                  cases hmerged : mergeAt? state (state.pending.size - 2) with
                  | none => simp
                  | some merged =>
                      simp only [Option.bind_some]
                      by_cases hsuccess :
                          merged.returnCode = 0 ∧ !merged.fuelExhausted
                      · rw [if_pos hsuccess, if_pos hsuccess]
                        exact ih merged.state power
                      · rw [if_neg hsuccess, if_neg hsuccess]
                        rfl
                · rw [if_neg hcollapse, if_neg hcollapse,
                    TraceResult.erase_map, erase_setTopPowerTraced]
                  cases hset : setTopPower? state power with
                  | none => simp
                  | some after =>
                      simp only [Option.map_some]
                      rfl
      · rw [if_neg hmany, if_neg hmany, TraceResult.erase_map,
          erase_setTopPowerTraced]
        cases hset : setTopPower? state power with
        | none => simp
        | some after =>
            simp only [Option.map_some]
            rfl

/-- Unconditional raw-domain erasure for the complete traced
`found_new_run` evaluator. -/
theorem erase_foundNewRunTraced
    (state : MergeState κ ν) (n2 : Nat) :
    (foundNewRunTraced? state n2).erase = foundNewRun? state n2 := by
  unfold foundNewRunTraced? foundNewRun?
  by_cases hempty : state.pending.isEmpty = true
  · rw [if_pos hempty, if_pos hempty]
    rfl
  · rw [if_neg hempty, if_neg hempty, TraceResult.erase_bind,
      TraceResult.erase_pendingRunRead]
    have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi :
        (Int.ofNat (state.pending.size - 1)).toNat =
          state.pending.size - 1 := rfl
    rw [htoi]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp
    | some top =>
        simp only [Option.bind_some]
        let guard :=
          ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < n2) &&
            decide (n2 ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat + n2 ≤
              state.listlen.toNat))
        by_cases hguard : guard = true
        · have hguard' :
              ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
                (0 : PySSize).slt top.len && decide (0 < n2) &&
                decide (n2 ≤ PY_SSIZE_T_MAX) &&
                decide (top.base - state.basekeys + top.len.toNat + n2 ≤
                  state.listlen.toNat)) = true := hguard
          simp only [hguard', if_true]
          let powered := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          by_cases hstopped : (!powered.stopped) = true
          · have hstopped' :
                (!(powerloopTraced
                  (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
                  (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
                hstopped
            simp only [hstopped', if_true]
            simp [TraceResult.erase_markFuelExhausted]
            rfl
          · have hstopped' : ¬
                (!(powerloopTraced
                  (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
                  (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
                hstopped
            simp only [hstopped']
            exact erase_foundNewRunLoopTraced_of_mergeAt erase_mergeAtTraced
              _ _ _
        · have hguard' : ¬
              ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
                (0 : PySSize).slt top.len && decide (0 < n2) &&
                decide (n2 ≤ PY_SSIZE_T_MAX) &&
                decide (top.base - state.basekeys + top.len.toNat + n2 ≤
                  state.listlen.toNat)) = true := hguard
          simp only [hguard']
          rfl

end CPythonListsort
