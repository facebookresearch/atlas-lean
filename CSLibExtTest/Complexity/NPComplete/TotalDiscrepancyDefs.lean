/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TotalDiscrepancyDefs
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TotalDiscrepancyInstance) :
    totalDiscrepancyDec (bitEncode i) = true ↔ WellFormed i ∧ TotalDiscrepancyFeasible i := by
  simp [totalDiscrepancyDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : totalDiscrepancyDec [true] = false := by
  have h : bitDecode (α := TotalDiscrepancyInstance) [true] = none := rfl
  simp [totalDiscrepancyDec, h]

/-- Two length-`2` tasks preferring midtimes `1` and `3` run back to back from time `0`
with zero total discrepancy. -/
example :
    totalDiscrepancyDec (bitEncode (([(2, 1), (2, 3)], 1) : TotalDiscrepancyInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun t => if (t : ℕ) = 0 then 0 else 2, ?_, ?_⟩
  · intro a b hab
    have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
    rcases key a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [taskLength]
  · rw [show (Finset.univ : Finset (Task ([(2, 1), (2, 3)], 1))) = {0, 1} by decide,
      Finset.sum_pair (by decide)]
    simp [taskLength, preferredMidtime]
    norm_num

/-- Two length-`2` tasks that both prefer midtime `1` have midtimes at least `2` apart, so
their total discrepancy is at least `2 > 1`. -/
example :
    totalDiscrepancyDec (bitEncode (([(2, 1), (2, 1)], 1) : TotalDiscrepancyInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, s, hs, hsum⟩
  have h := hs 0 1 (by decide)
  rw [show (Finset.univ : Finset (Task ([(2, 1), (2, 1)], 1))) = {0, 1} by decide,
    Finset.sum_pair (by decide)] at hsum
  simp [taskLength, preferredMidtime] at hsum h
  rcases h with h | h <;>
    linarith [le_abs_self (s 0), neg_abs_le (s 0), le_abs_self (s 1), neg_abs_le (s 1)]

/-- The rejected instance is well formed, so the rejection comes from the discrepancy bound. -/
example : WellFormed (([(2, 1), (2, 1)], 1) : TotalDiscrepancyInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy
