/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TensorRankPrimeFieldDefs

namespace MetaMathlibExt.Complexity.NPComplete.TensorRankPrimeField

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Complexity.Algebraic.MatrixMultiplicationExponent
  (HasTrilinearRankAtMost RankOneTrilinearTerm RankOneTrilinearTerm.eval)

private theorem accepts_encoding (p : ℕ) (i : TensorRankPrimeFieldInstance) :
    tensorRankPrimeFieldDec p (bitEncode i) = true ↔
      WellFormed p i ∧ TensorRankPrimeFieldFeasible p i := by
  simp [tensorRankPrimeFieldDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every prime parameter. -/
example (p : ℕ) : tensorRankPrimeFieldDec p [true] = false := by
  have h : bitDecode (α := TensorRankPrimeFieldInstance) [true] = none := rfl
  simp [tensorRankPrimeFieldDec, h]

/-- A one-by-one-by-one tensor with entry `x` is the single rank-one term `1 ⊗ 1 ⊗ x`. -/
private theorem single_rank_one (p x : ℕ) :
    TensorRankPrimeFieldFeasible p ([[[x]]], 1) := by
  refine ⟨[⟨fun _ => 1, fun _ => 1, fun _ => (x : ZMod p)⟩], le_rfl, ?_⟩
  intro a b c
  have ha : (a : ℕ) = 0 := by have := a.isLt; simp [dim₁] at this; omega
  have hb : (b : ℕ) = 0 := by have := b.isLt; simp [dim₂] at this; omega
  have hc : (c : ℕ) = 0 := by have := c.isLt; simp [dim₃] at this; omega
  simp [tensor, entry, RankOneTrilinearTerm.eval, ha, hb, hc]

/-- A nonzero one-by-one-by-one tensor has no decomposition with zero terms. -/
private theorem not_rank_zero (p x : ℕ) (hx : (x : ZMod p) ≠ 0) :
    ¬ TensorRankPrimeFieldFeasible p ([[[x]]], 0) := by
  rintro ⟨terms, hlen, heval⟩
  have hnil : terms = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hnil
  have a : Fin (dim₁ ([[[x]]], 0)) := ⟨0, by simp [dim₁]⟩
  have b : Fin (dim₂ ([[[x]]], 0)) := ⟨0, by simp [dim₂]⟩
  have c : Fin (dim₃ ([[[x]]], 0)) := ⟨0, by simp [dim₃]⟩
  have ha : (a : ℕ) = 0 := by have := a.isLt; simp [dim₁] at this; omega
  have hb : (b : ℕ) = 0 := by have := b.isLt; simp [dim₂] at this; omega
  have hc : (c : ℕ) = 0 := by have := c.isLt; simp [dim₃] at this; omega
  exact hx (by simpa [tensor, entry, ha, hb, hc] using heval a b c)

/-- Over `ZMod 2`, the tensor `[[[1]]]` has rank at most one. -/
example :
    tensorRankPrimeFieldDec 2 (bitEncode (([[[1]]], 1) : TensorRankPrimeFieldInstance)) =
      true :=
  (accepts_encoding 2 _).2 ⟨by unfold WellFormed; decide, single_rank_one 2 1⟩

/-- Over `ZMod 2`, the tensor `[[[1]]]` does not have rank zero. -/
example :
    tensorRankPrimeFieldDec 2 (bitEncode (([[[1]]], 0) : TensorRankPrimeFieldInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  exact fun h => not_rank_zero 2 1 (by decide) h.2

/-- Over `ZMod 3`, the tensor `[[[2]]]` has rank at most one. -/
example :
    tensorRankPrimeFieldDec 3 (bitEncode (([[[2]]], 1) : TensorRankPrimeFieldInstance)) =
      true :=
  (accepts_encoding 3 _).2 ⟨by unfold WellFormed; decide, single_rank_one 3 2⟩

/-- Over `ZMod 3`, the tensor `[[[2]]]` does not have rank zero. -/
example :
    tensorRankPrimeFieldDec 3 (bitEncode (([[[2]]], 0) : TensorRankPrimeFieldInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  exact fun h => not_rank_zero 3 2 (by decide) h.2

/-- Over `ZMod 2`, the entry `2` is not a field element, so the tensor accepted over
`ZMod 3` is rejected as malformed. -/
example :
    tensorRankPrimeFieldDec 2 (bitEncode (([[[2]]], 1) : TensorRankPrimeFieldInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨hwf, -⟩
  revert hwf
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.TensorRankPrimeField
