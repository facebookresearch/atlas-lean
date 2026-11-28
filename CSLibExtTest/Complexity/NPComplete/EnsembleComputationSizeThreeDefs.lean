/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EnsembleComputationSizeThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open EnsembleComputation (EnsembleComputationInstance EnsembleComputationFeasible operandValue)

private theorem accepts_encoding (i : EnsembleComputationInstance) :
    ensembleComputationSizeThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ EnsembleComputationFeasible i := by
  simp [ensembleComputationSizeThreeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : ensembleComputationSizeThreeDec [true] = false := by
  have h : bitDecode (α := EnsembleComputationInstance) [true] = none := rfl
  simp [ensembleComputationSizeThreeDec, h]

/-- The results of `z₀ ← {0} ∪ {1}` and `z₁ ← z₀ ∪ {2}`. -/
private def zs : Fin 2 → Finset (Fin 3) := fun t => if t.1 = 0 then {0, 1} else {0, 1, 2}

/-- The left operands `{0}` and `z₀`. -/
private def xs : Fin 2 → Fin 3 ⊕ Fin 2 := fun t => if t.1 = 0 then .inl 0 else .inr 0

/-- The right operands `{1}` and `{2}`. -/
private def ys : Fin 2 → Fin 3 ⊕ Fin 2 := fun t => if t.1 = 0 then .inl 1 else .inl 2

/-- With `J = 2`, two disjoint unions build the three-element member `{0, 1, 2}`. -/
example : ensembleComputationSizeThreeDec (bitEncode ((3, [[0, 1, 2]], 2) :
    EnsembleComputationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed EnsembleComputation.WellFormed; decide,
    2, le_refl _, zs, xs, ys, by decide, by decide, ?_, ?_, ?_⟩
  · intro t
    unfold zs xs ys operandValue
    revert t
    decide
  · intro t
    unfold zs xs ys operandValue
    revert t
    decide
  · intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact ⟨1, by decide⟩

/-- With `J = 1`, the single union has at most two elements, so `{0, 1, 2}` is out of reach. -/
example : ensembleComputationSizeThreeDec (bitEncode ((3, [[0, 1, 2]], 1) :
    EnsembleComputationInstance)) = false := by
  cases h : ensembleComputationSizeThreeDec
      (bitEncode ((3, [[0, 1, 2]], 1) : EnsembleComputationInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, j, hj, z, x, y, hx, hy, -, hz, hc⟩ := (accepts_encoding _).1 h
    obtain ⟨t, ht⟩ := hc [0, 1, 2] (List.mem_singleton_self _)
    have h0 : t.1 = 0 := by have := t.2; simp at hj; omega
    have hs : ∀ (w : Fin 3 ⊕ Fin j), (∀ k, w = .inr k → k < t) →
        (operandValue z w).card ≤ 1 := by
      rintro (a | k) hw
      · simp [operandValue]
      · have := hw k rfl
        exact absurd (Fin.lt_def.1 this) (by omega)
    have h₁ := hs _ (hx t)
    have h₂ := hs _ (hy t)
    have h₃ := Finset.card_union_le (operandValue z (x t)) (operandValue z (y t))
    rw [← hz t, ht] at h₃
    exact absurd (h₃.trans (Nat.add_le_add h₁ h₂)) (by decide)

/-- A four-element member is outside the size-three restriction: the instance is computable
with three disjoint unions, but it is not well formed, so it is rejected. -/
example : ensembleComputationSizeThreeDec (bitEncode ((4, [[0, 1, 2, 3]], 3) :
    EnsembleComputationInstance)) = false := by
  have hc : EnsembleComputationFeasible
      ((4, [[0, 1, 2, 3]], 3) : EnsembleComputationInstance) := by
    refine ⟨3, le_refl _, fun t => if t.1 = 0 then {0, 1} else if t.1 = 1 then {0, 1, 2}
      else {0, 1, 2, 3}, fun t => if t.1 = 0 then .inl 0 else if t.1 = 1 then .inr 0
      else .inr 1, fun t => if t.1 = 0 then .inl 1 else if t.1 = 1 then .inl 2 else .inl 3,
      by decide, by decide, ?_, ?_, ?_⟩
    · intro t; unfold operandValue; revert t; decide
    · intro t; unfold operandValue; revert t; decide
    · intro c hc
      obtain rfl := List.mem_singleton.1 hc
      exact ⟨2, by decide⟩
  have hw : ¬ WellFormed ((4, [[0, 1, 2, 3]], 3) : EnsembleComputationInstance) :=
    fun h => absurd (h.2 _ (List.mem_singleton_self _)) (by decide)
  simp [ensembleComputationSizeThreeDec, bitDecode_bitEncode, hw]

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree
