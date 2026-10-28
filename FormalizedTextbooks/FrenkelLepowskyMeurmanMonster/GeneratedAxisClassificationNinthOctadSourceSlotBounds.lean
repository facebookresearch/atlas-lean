/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotShapeCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourierBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotExceptional

/-! Sparse original octad coefficients are identified from complete genuine source-row
certificates. All original source signs, integer numerators and Fourier rows are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every displayed octad marking has original signed Fourier numerator minus16. -/
theorem generatedNinth_octad_slot_marking_integer (o : Fin 759) (e : Fin 64)
    (h : o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    generatedNinthFinalOctadSlotFastNumerator o e = -16 := by
  obtain ⟨rfl, he⟩ := h
  simpa only [he, ite_true] using generatedNinth_octad_exceptional_integer e

/-- Every other original octad Fourier numerator has absolute value at most four. -/
theorem generatedNinth_octad_slot_nonmarking_integer (o : Fin 759) (e : Fin 64)
    (h : ¬ (o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)) :
    |generatedNinthFinalOctadSlotFastNumerator o e| ≤ 4 := by
  by_cases ho : o = 459
  · have he : e ∉ generatedNinthOctadMarkedSigns := by
      intro he
      exact h ⟨ho, he⟩
    subst o
    simpa only [he, ite_false] using generatedNinth_octad_exceptional_integer e
  · rcases generatedNinth_octad_source_shape o with hbad | htwo | hfour
    · exact (ho hbad).elim
    · exact generatedNinth_octad_two_slot_fourier_abs_le o htwo e
    · exact generatedNinth_octad_four_slot_fourier_abs_le o hfour e

/-- Complete original source certificates give the actual coefficient minus one eighth
at every displayed octad marking. -/
theorem generatedNinth_final_octad_marking_coefficient_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) (h : o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) = -1 / 8 := by
  rw [generatedNinth_final_octad_slot_fast_of_certificates hcert,
    generatedNinth_octad_slot_marking_integer o e h]
  norm_num

/-- Complete original source certificates bound every other actual octad coefficient
by one thirty-second in absolute value. -/
theorem generatedNinth_final_octad_nonmarking_bound_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) (h : ¬ (o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| ≤ 1 / 32 := by
  have hb := generatedNinth_octad_slot_nonmarking_integer o e h
  have hc : ((|generatedNinthFinalOctadSlotFastNumerator o e| : ℤ) : ℝ) ≤ 4 := by
    exact_mod_cast hb
  rw [generatedNinth_final_octad_slot_fast_of_certificates hcert, abs_div,
    show |(128 : ℝ)| = 128 by norm_num, ← Int.cast_abs]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
  norm_num
  simpa only [Int.cast_abs] using hc

/-- Complete original source certificates identify exactly the actual octad rows whose
coefficient has absolute value one eighth. -/
theorem generatedNinth_final_octad_marking_iff_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k) (o : Fin 759) (e : Fin 64) :
    |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
      o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns := by
  constructor
  · intro heq
    by_contra h
    have hb := generatedNinth_final_octad_nonmarking_bound_of_certificates hcert o e h
    rw [heq] at hb
    norm_num at hb
  · intro h
    rw [generatedNinth_final_octad_marking_coefficient_of_certificates hcert o e h]
    norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
