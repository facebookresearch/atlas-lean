/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SparseApproximationDefs

namespace MetaMathlibExt.Complexity.NPComplete.SparseApproximation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open QuadraticProgramming (RatCode ratVal)

private theorem accepts_encoding (i : SparseApproximationInstance) :
    sparseApproximationDec (bitEncode i) = true ↔
      WellFormed i ∧ SparseApproximationFeasible i := by
  simp [sparseApproximationDec, bitDecode_bitEncode]

/-- The system `x₀ = 1` with tolerance `ε = 1/2` and sparsity bound `k`. -/
private abbrev system (k : ℕ) : SparseApproximationInstance :=
  (1, [[((1, 0), 1)]], [((1, 0), 1)], ((1, 0), 2), k)

/-- A lone continuation bit is a truncated instance encoding. -/
example : sparseApproximationDec [true] = false := by
  have h : bitDecode (α := SparseApproximationInstance) [true] = none := rfl
  simp [sparseApproximationDec, h]

/-- With one nonzero entry allowed, `x = (1)` solves the system exactly. -/
example : sparseApproximationDec (bitEncode (system 1)) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨rfl, by decide, by decide, by decide, by simp [ratVal]⟩, fun _ => 1, ?_, ?_⟩
  · exact (Finset.card_le_univ _).trans (by simp)
  · simp [entry, rhs, ratVal]

/-- With no nonzero entry allowed, `x = 0` leaves the residual `1 > 1/2`. -/
example : sparseApproximationDec (bitEncode (system 0)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, x, hk, hres⟩ := (accepts_encoding _).1 hacc
  have hx : x 0 = 0 := by
    by_contra hne
    have : (0 : Fin 1) ∈ Finset.univ.filter fun c => x c ≠ 0 := by simpa using hne
    exact absurd (Finset.card_pos.2 ⟨_, this⟩) (by simpa using hk)
  simp [entry, rhs, ratVal, hx] at hres
  norm_num at hres

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (system 0) :=
  ⟨rfl, by decide, by decide, by decide, by simp [ratVal]⟩

end MetaMathlibExt.Complexity.NPComplete.SparseApproximation
