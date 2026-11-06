/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Exact code-labelled integer numerators retain every middle row in the final octad transform. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The cleared final octad numerator, keyed by the original code label and all preferred signs. -/
def generatedSixthFinalOctadNumerator (d : Fin 4096) (e : Fin 64) : ℤ :=
  ∑ j : Fin 273, if generatedSixthMiddleOctadCode j = d then
    trialityIntegerMatrix e (generatedSixthMiddleOctadSign j) *
      generatedSixthMiddleOctadWeight j else 0

private theorem octad_eq_code (j : Fin 273) (o : Fin 759) :
    generatedSixthMiddleOctad j = o ↔
      generatedSixthMiddleOctadCode j = golayOctadLabel o := by
  constructor
  · intro h
    simpa only [generatedSixthMiddleOctad_label] using congrArg golayOctadLabel h
  · intro h
    apply golayOctadLabel_injective
    simpa only [generatedSixthMiddleOctad_label] using h

/-- Every actual final octad coefficient is the whole original signed DH numerator over 32. -/
theorem generatedSixth_final_octad_coordinate (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedSixthFinalOctadNumerator (golayOctadLabel o) e : ℝ) / 32 := by
  rw [generatedSixthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  simp_rw [generatedSixth_middle_octad_sparse, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (j : Fin 273) :
      (∑ f : Fin 64, trialityRealMatrix e f *
        (if generatedSixthMiddleOctadOutput j = Sum.inr (Sum.inl (o, f)) then
          (generatedSixthMiddleOctadWeight j : ℝ) / 4 else 0)) =
      if generatedSixthMiddleOctadCode j = golayOctadLabel o then
        trialityRealMatrix e (generatedSixthMiddleOctadSign j) *
          ((generatedSixthMiddleOctadWeight j : ℝ) / 4) else 0 := by
    simp only [generatedSixthMiddleOctadOutput, generatedSixthMiddleOctadTargetCoordinates,
      Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases ho : generatedSixthMiddleOctad j = o
    · simp only [ho, true_and, mul_ite, mul_zero]
      simp [(octad_eq_code j o).mp ho]
    · have hc := mt (octad_eq_code j o).mpr ho
      simp [ho, hc]
  simp_rw [hf]
  simp only [generatedSixthFinalOctadNumerator, Int.cast_sum, Int.cast_ite,
    Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : generatedSixthMiddleOctadCode j = golayOctadLabel o
  · simp only [hc, ite_true, trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply,
      Int.coe_castRingHom]
    ring
  · simp [hc]

/-- Every octad outside the genuine occurring code families has zero final coefficient. -/
theorem generatedSixth_final_octad_zero_outside (o : Fin 759) (e : Fin 64)
    (ho : ¬ ∃ j : Fin 273, generatedSixthMiddleOctad j = o) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  rw [generatedSixth_final_octad_coordinate]
  have hc : generatedSixthFinalOctadNumerator (golayOctadLabel o) e = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h : generatedSixthMiddleOctadCode j ≠ golayOctadLabel o :=
      fun h => ho ⟨j, (octad_eq_code j o).mpr h⟩
    simp only [h, ite_false]
  rw [hc, Int.cast_zero, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
