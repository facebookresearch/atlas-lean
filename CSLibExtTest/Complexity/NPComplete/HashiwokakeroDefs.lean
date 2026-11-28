/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HashiwokakeroDefs
-- `Fin.sum_univ_two`, used to expand the bridge sums of two islands.
import Mathlib.Algebra.BigOperators.Fin

namespace MetaMathlibExt.Complexity.NPComplete.Hashiwokakero

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HashiwokakeroInstance) :
    hashiwokakeroDec (bitEncode i) = true ↔ WellFormed i ∧ HashiwokakeroFeasible i := by
  simp [hashiwokakeroDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hashiwokakeroDec [true] = false := by
  have h : bitDecode (α := HashiwokakeroInstance) [true] = none := rfl
  simp [hashiwokakeroDec, h]

/-- Two islands with label `2` in one row, three columns apart: a double bridge joins them. -/
example : hashiwokakeroDec
    (bitEncode ([(0, 0, 2), (3, 0, 2)] : HashiwokakeroInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    fun a b => if a = b then 0 else 2, by decide, by decide, ?_, ?_, by decide, ?_⟩
  · unfold Visible
    decide
  · unfold Cross
    decide
  · intro a b
    by_cases h : a = b
    · exact h ▸ .refl _
    · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl (by simp [h])⟩)

/-- Two islands in one row with labels `1` and `2` are well formed, but a bridge count is shared by
both ends, so the two labels would have to agree. -/
example : hashiwokakeroDec
    (bitEncode ([(0, 0, 1), (1, 0, 2)] : HashiwokakeroInstance)) = false := by
  have h : ¬ HashiwokakeroFeasible [(0, 0, 1), (1, 0, 2)] := by
    rintro ⟨bridges, symm, -, visible, -, labels, -⟩
    have loop : ∀ a, bridges a a = 0 := fun a =>
      Nat.eq_zero_of_not_pos fun h => (visible a a h).1 rfl
    have h₀ : ∑ b : Fin 2, bridges 0 b = 1 := labels 0
    have h₁ : ∑ b : Fin 2, bridges 1 b = 2 := labels 1
    rw [Fin.sum_univ_two] at h₀ h₁
    have := symm 0 1
    have := loop 0
    have := loop 1
    omega
  simpa [hashiwokakeroDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Hashiwokakero
