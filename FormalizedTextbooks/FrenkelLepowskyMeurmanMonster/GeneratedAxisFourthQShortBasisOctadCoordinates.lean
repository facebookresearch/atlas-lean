/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fourth_octad_eq_code (j : Fin 63) (o : Fin 759) :
    generatedFourthEvenRootOctad j = o ↔
      generatedFourthEvenRootCode j = golayOctadLabel o := by
  constructor
  · intro h
    simpa only [generatedFourthEvenRootOctad_label] using congrArg golayOctadLabel h
  · intro h
    apply golayOctadLabel_injective
    simpa only [generatedFourthEvenRootOctad_label] using h

private theorem fourth_phase_integer (c : ZMod 2) :
    qSign c = ((if c = 0 then 1 else -1 : ℤ) : ℝ) := by
  have h : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h with rfl | rfl <;> simp

/-- Every actual final octad coefficient is exactly its integer DH numerator divided by eight. -/
theorem generatedFourthQShortBasis_octad_coordinate (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedFourthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedFourthQShortBasisOctadNumerator (golayOctadLabel o) e : ℝ) / 8 := by
  rw [generatedFourthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  simp_rw [generatedFourth_local_short, generatedFourth_middle_octad_sparse_cache]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (j : Fin 63) :
      (∑ f : Fin 64, trialityRealMatrix e f *
        (if generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, f)) then
          qSign (generatedFourthEvenCoefficientCache j) else 0)) =
      if generatedFourthEvenRootCode j = golayOctadLabel o then
        trialityRealMatrix e (generatedFourthEvenRootSign j) *
          qSign (generatedFourthEvenCoefficientCache j) else 0 := by
    simp only [generatedFourthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl.injEq,
      Prod.mk.injEq]
    by_cases ho : generatedFourthEvenRootOctad j = o
    · simp only [ho, true_and, mul_ite, mul_zero]
      simp [(fourth_octad_eq_code j o).mp ho]
    · have hc := mt (fourth_octad_eq_code j o).mpr ho
      simp [ho, hc]
  simp_rw [hf]
  simp only [generatedFourthQShortBasisOctadNumerator, Int.cast_sum, Int.cast_ite,
    Int.cast_mul, Int.cast_one, Int.cast_neg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : generatedFourthEvenRootCode j = golayOctadLabel o
  · simp only [hc, ↓reduceIte, trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply,
      Int.coe_castRingHom, fourth_phase_integer, Int.cast_ite, Int.cast_one, Int.cast_neg]
    ring
  · simp [hc]

/-- An octad outside the forty-seven actual code families has zero final coefficient. -/
theorem generatedFourthQShortBasis_octad_zero_outside (o : Fin 759) (e : Fin 64)
    (ho : ¬∃ j : Fin 63, generatedFourthEvenRootOctad j = o) :
    (griessConwayEncode generatedFourthAxis).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  rw [generatedFourthQShortBasis_octad_coordinate]
  have hc : generatedFourthQShortBasisOctadNumerator (golayOctadLabel o) e = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h : generatedFourthEvenRootCode j ≠ golayOctadLabel o :=
      fun h => ho ⟨j, (fourth_octad_eq_code j o).mpr h⟩
    simp only [h, ite_false]
  rw [hc, Int.cast_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
