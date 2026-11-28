/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EnsembleComputationNonDisjointDefs

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputationNonDisjoint

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open EnsembleComputation (EnsembleComputationInstance operandValue)

private theorem accepts_encoding (i : EnsembleComputationInstance) :
    ensembleComputationNonDisjointDec (bitEncode i) = true ↔
      WellFormed i ∧ EnsembleComputationNonDisjointFeasible i := by
  simp [ensembleComputationNonDisjointDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : ensembleComputationNonDisjointDec [true] = false := by
  have h : bitDecode (α := EnsembleComputationInstance) [true] = none := rfl
  simp [ensembleComputationNonDisjointDec, h]

/-- The singleton member `{0}` is the union `{0} ∪ {0}` of two overlapping operands, which the
non-disjoint variant allows. -/
example : ensembleComputationNonDisjointDec (bitEncode ((1, [[0]], 1) :
    EnsembleComputationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed EnsembleComputation.WellFormed; decide,
    1, le_refl _, fun _ => {0}, fun _ => .inl 0, fun _ => .inl 0, by decide, by decide, ?_, ?_⟩
  · intro t; unfold operandValue; revert t; decide
  · intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact ⟨0, by decide⟩

/-- With `J = 2`, the unions `z₀ ← {0} ∪ {1}` and `z₁ ← z₀ ∪ {2}` build `{0, 1, 2}`. -/
example : ensembleComputationNonDisjointDec (bitEncode ((3, [[0, 1, 2]], 2) :
    EnsembleComputationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed EnsembleComputation.WellFormed; decide,
    2, le_refl _, fun t => if t.1 = 0 then {0, 1} else {0, 1, 2},
    fun t => if t.1 = 0 then .inl 0 else .inr 0, fun t => if t.1 = 0 then .inl 1 else .inl 2,
    by decide, by decide, ?_, ?_⟩
  · intro t; unfold operandValue; revert t; decide
  · intro c hc
    obtain rfl := List.mem_singleton.1 hc
    exact ⟨1, by decide⟩

/-- With `J = 1`, the single union has at most two elements, so `{0, 1, 2}` is out of reach
even without disjointness. -/
example : ensembleComputationNonDisjointDec (bitEncode ((3, [[0, 1, 2]], 1) :
    EnsembleComputationInstance)) = false := by
  cases h : ensembleComputationNonDisjointDec
      (bitEncode ((3, [[0, 1, 2]], 1) : EnsembleComputationInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, j, hj, z, x, y, hx, hy, hz, hc⟩ := (accepts_encoding _).1 h
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

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputationNonDisjoint
