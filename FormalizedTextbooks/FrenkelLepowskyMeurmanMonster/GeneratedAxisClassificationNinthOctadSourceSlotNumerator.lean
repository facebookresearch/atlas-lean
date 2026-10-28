/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourierData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotExpansion

/-! The cached eight-slot calculation agrees with the original complete signed Fourier
coefficient, retaining the independent full source-row certificate family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Every checked cached Fourier numerator equals the complete original signed slot sum. -/
theorem generatedNinth_final_octad_slot_fast_numerator_actual (o : Fin 759) (e : Fin 64) :
    generatedNinthFinalOctadSlotNumerator o e =
      generatedNinthFinalOctadSlotFastNumerator o e := by
  classical
  unfold generatedNinthFinalOctadSlotNumerator generatedNinthFinalOctadSlotFastNumerator
  apply Finset.sum_congr rfl
  intro j _
  rw [← generatedNinth_octad_slot_numerator_actual]
  by_cases hj : generatedNinthOctadSourceSlotWord o j ≠ 0
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj, mul_zero]

/-- Every actual final octad coefficient is the checked cached slot numerator over128. -/
theorem generatedNinth_final_octad_slot_fast_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedNinthFinalOctadSlotFastNumerator o e : ℝ) / 128 := by
  rw [← generatedNinth_final_octad_slot_fast_numerator_actual]
  exact generatedNinth_final_octad_slot_of_certificates hcert o e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
