/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddSparseIndex

/-! The complete original middle odd coefficients as exact finite three-slot code rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 10000

private def sourcePoint (r : Fin 552) (d : Fin 2048) (i : Fin 24) : ℤ :=
  let a := generatedSeventhXiOddSource r
  generatedSeventhXiShortInputWeight a.1 a.2 *
    nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2) *
    (if generatedSeventhXiOddSourcePredicate r ∧
        generatedSeventhXiShortDescriptor a.1 a.2 1 = d.val ∧
        generatedSeventhXiShortDescriptor a.1 a.2 2 = i.val then 1 else 0)

private theorem sourceSum (f : Fin 2 × Fin 276 → ℤ) :
    (∑ s : Fin 2, ∑ p : Fin 276, f (s, p)) =
      ∑ r : Fin 552, f (generatedSeventhXiOddSource r) := by
  rw [← Fintype.sum_prod_type]
  have h := (finProdFinEquiv : Fin 2 × Fin 276 ≃ Fin 552).symm.sum_comp f
  have he (r : Fin 552) :
      (finProdFinEquiv : Fin 2 × Fin 276 ≃ Fin 552).symm r =
        generatedSeventhXiOddSource r := by rfl
  simpa only [he] using h.symm

private theorem numerator_source_sum (d : Fin 2048) (i : Fin 24) :
    generatedSeventhXiMiddleOddNumerator d i = ∑ r : Fin 552, sourcePoint r d i := by
  unfold generatedSeventhXiMiddleOddNumerator
  have h := sourceSum (fun a : Fin 2 × Fin 276 =>
    generatedSeventhXiShortInputWeight a.1 a.2 *
      nortonUIntegerSign (generatedSeventhXiShortPhaseBit a.1 a.2 : ZMod 2) *
      (if generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 0 ∧
          generatedSeventhXiShortDescriptor a.1 a.2 0 ≠ 1 ∧
          generatedSeventhXiShortDescriptor a.1 a.2 1 = d.val ∧
          generatedSeventhXiShortDescriptor a.1 a.2 2 = i.val then 1 else 0))
  simpa only [sourcePoint, generatedSeventhXiOddSourcePredicate, and_assoc] using h

/-- The exact signed coefficient selected from one certified code row. -/
def generatedSeventhXiOddRowCoefficient (d : Fin 2048) (i : Fin 24)
    (g : Fin 232) (k : Fin 3) : ℤ :=
  generatedSeventhXiOddWeights g k *
    (if generatedSeventhXiOddCodes g = d.val ∧ generatedSeventhXiOddPositions g k = i.val
      then 1 else 0)

private theorem entry_point (d : Fin 2048) (i : Fin 24) (g : Fin 232) (k : Fin 3) :
    (if h : generatedSeventhXiOddEntries g k < 552 then
      sourcePoint ⟨generatedSeventhXiOddEntries g k, h⟩ d i else 0) =
      generatedSeventhXiOddRowCoefficient d i g k := by
  have h := generatedSeventhXiOdd_entry g k
  by_cases hv : generatedSeventhXiOddEntries g k < 552
  · rw [dite_eq_left hv]
    rw [dite_eq_left hv] at h
    dsimp only at h
    have hp : generatedSeventhXiOddSourcePredicate
        ⟨generatedSeventhXiOddEntries g k, hv⟩ := ⟨h.2.2.1, h.2.2.2.1⟩
    dsimp only [sourcePoint, generatedSeventhXiOddRowCoefficient]
    rw [← h.2.2.2.2.1, ← h.2.2.2.2.2.1, ← h.2.2.2.2.2.2]
    simp only [hp, true_and]
  · rw [dite_eq_right hv]
    rw [dite_eq_right hv] at h
    simp only [generatedSeventhXiOddRowCoefficient, h.2, zero_mul]

/-- All original middle odd coefficients equal the complete sparse row sum. -/
theorem generatedSeventhXiOdd_sparse_coefficient (d : Fin 2048) (i : Fin 24) :
    generatedSeventhXiMiddleOddNumerator d i =
      ∑ g : Fin 232, ∑ k : Fin 3, generatedSeventhXiOddRowCoefficient d i g k := by
  rw [numerator_source_sum]
  have hf : (∑ r : Fin 552, sourcePoint r d i) =
      ∑ r ∈ Finset.univ.filter generatedSeventhXiOddSourcePredicate, sourcePoint r d i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hp : generatedSeventhXiOddSourcePredicate r
    · simp only [hp, ite_true]
    · simp only [sourcePoint, hp, false_and, ite_false, mul_zero]
  rw [hf, generatedSeventhXiOdd_sparse_sum]
  have he : (∑ z ∈ Finset.univ.filter
        (fun z : Fin 232 × Fin 3 => generatedSeventhXiOddEntries z.1 z.2 < 552),
      if h : generatedSeventhXiOddEntries z.1 z.2 < 552 then
        sourcePoint ⟨generatedSeventhXiOddEntries z.1 z.2, h⟩ d i else 0) =
      ∑ z : Fin 232 × Fin 3, generatedSeventhXiOddRowCoefficient d i z.1 z.2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hv : generatedSeventhXiOddEntries z.1 z.2 < 552
    · rw [ite_eq_left hv, dite_eq_left hv]
      have h := entry_point d i z.1 z.2
      rw [dite_eq_left hv] at h
      exact h
    · rw [ite_eq_right hv]
      have h := entry_point d i z.1 z.2
      simpa only [dite_eq_right hv] using h
  rw [he, Fintype.sum_prod_type]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
