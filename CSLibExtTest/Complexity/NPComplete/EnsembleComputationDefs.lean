/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EnsembleComputationDefs

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputation

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : EnsembleComputationInstance) :
    ensembleComputationDec (bitEncode i) = true ↔
      WellFormed i ∧ EnsembleComputationFeasible i := by
  simp [ensembleComputationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : ensembleComputationDec [true] = false := by
  have h : bitDecode (α := EnsembleComputationInstance) [true] = none := rfl
  simp [ensembleComputationDec, h]

/-- The results of `z₀ ← {0} ∪ {1}` and `z₁ ← z₀ ∪ {2}`. -/
private def zs : Fin 2 → Finset (Fin 3) := fun t => if t.1 = 0 then {0, 1} else {0, 1, 2}

/-- The left operands `{0}` and `z₀`. -/
private def xs : Fin 2 → Fin 3 ⊕ Fin 2 := fun t => if t.1 = 0 then .inl 0 else .inr 0

/-- The right operands `{1}` and `{2}`. -/
private def ys : Fin 2 → Fin 3 ⊕ Fin 2 := fun t => if t.1 = 0 then .inl 1 else .inl 2

/-- With `J = 2`, two disjoint unions build `{0, 1, 2}`. -/
example : ensembleComputationDec (bitEncode ((3, [[0, 1, 2]], 2) :
    EnsembleComputationInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 2, le_refl _, zs, xs, ys,
    by decide, by decide, ?_, ?_, ?_⟩
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

/-- An operation whose operands are not earlier results unites two singletons. -/
private theorem card_first_le_two {m j : ℕ} (z : Fin j → Finset (Fin m))
    (x y : Fin j → Fin m ⊕ Fin j) (hx : ∀ t k, x t = .inr k → k < t)
    (hy : ∀ t k, y t = .inr k → k < t)
    (hz : ∀ t, z t = operandValue z (x t) ∪ operandValue z (y t)) (t : Fin j)
    (ht : t.1 = 0) : (z t).card ≤ 2 := by
  rw [hz t]
  refine (Finset.card_union_le _ _).trans ?_
  have hs : ∀ (w : Fin m ⊕ Fin j), (∀ k, w = .inr k → k < t) →
      (operandValue z w).card ≤ 1 := by
    rintro (a | k) hw
    · simp [operandValue]
    · have := hw k rfl
      exact absurd (Fin.lt_def.1 this) (by omega)
  have := hs _ (hx t); have := hs _ (hy t)
  omega

/-- With `J = 1`, the single union has at most two elements, so `{0, 1, 2}` is out of reach. -/
example : ensembleComputationDec (bitEncode ((3, [[0, 1, 2]], 1) :
    EnsembleComputationInstance)) = false := by
  cases h : ensembleComputationDec
      (bitEncode ((3, [[0, 1, 2]], 1) : EnsembleComputationInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, j, hj, z, x, y, hx, hy, -, hz, hc⟩ := (accepts_encoding _).1 h
    obtain ⟨t, ht⟩ := hc [0, 1, 2] (List.mem_singleton_self _)
    have h0 : t.1 = 0 := by have := t.2; simp at hj; omega
    have := card_first_le_two z x y hx hy hz t h0
    rw [ht] at this
    exact absurd this (by decide)

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
