/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeneralizedZeroOneAssignmentDefs
-- `Fin.sum_univ_two`, used to expand the row sums of a two-column matrix.
import Mathlib.Algebra.BigOperators.Fin

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : GeneralizedZeroOneAssignmentInstance) :
    generalizedZeroOneAssignmentDec (bitEncode i) = true ↔
      WellFormed i ∧ GeneralizedZeroOneAssignmentFeasible i := by
  simp [generalizedZeroOneAssignmentDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : generalizedZeroOneAssignmentDec [true] = false := by
  have h : bitDecode (α := GeneralizedZeroOneAssignmentInstance) [true] = none := rfl
  simp [generalizedZeroOneAssignmentDec, h]

/-- Two rows and two columns with unit weights, capacity `1` for the first row and `b₁` for the
second, costs `0` on the diagonal and `1` off it, and cost bound `1`. -/
private abbrev inst (b₁ : ℕ) : GeneralizedZeroOneAssignmentInstance :=
  (2, 2, [[(1, 0), (1, 0)], [(1, 0), (1, 0)]], [(1, 0), (b₁, 0)], [[0, 1], [1, 0]], 1)

/-- With both capacities `1`, assigning column `j` to row `j` meets both capacities at cost `0`.
-/
example : generalizedZeroOneAssignmentDec (bitEncode (inst 1)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    fun r c => if r.val = c.val then 1 else 0, ?_⟩
  unfold entryA entryB entryC intOf
  refine ⟨by decide, fun c => ⟨c, by simp, fun r hr => Fin.ext ?_⟩, by decide, by decide⟩
  by_contra hne
  simp [hne] at hr

/-- With the second capacity `0`, both columns must go to the first row, exceeding its capacity
`1`. -/
example : generalizedZeroOneAssignmentDec (bitEncode (inst 0)) = false := by
  have h : ¬ GeneralizedZeroOneAssignmentFeasible (inst 0) := by
    rintro ⟨X, -, huniq, hrow, -⟩
    have h₀ : ∑ c : Fin 2, entryA (inst 0) 0 c * (X 0 c : ℤ) ≤ entryB (inst 0) 0 := hrow 0
    have h₁ : ∑ c : Fin 2, entryA (inst 0) 1 c * (X 1 c : ℤ) ≤ entryB (inst 0) 1 := hrow 1
    rw [Fin.sum_univ_two] at h₀ h₁
    simp [entryA, entryB, intOf] at h₀ h₁
    obtain ⟨r₀, hr₀, -⟩ := huniq 0
    obtain ⟨r₁, hr₁, -⟩ := huniq 1
    have e₀ : X 0 0 = 1 ∨ X 1 0 = 1 := (Fin.exists_fin_two (p := fun r => X r 0 = 1)).1 ⟨r₀, hr₀⟩
    have e₁ : X 0 1 = 1 ∨ X 1 1 = 1 := (Fin.exists_fin_two (p := fun r => X r 1 = 1)).1 ⟨r₁, hr₁⟩
    omega
  simpa [generalizedZeroOneAssignmentDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment
