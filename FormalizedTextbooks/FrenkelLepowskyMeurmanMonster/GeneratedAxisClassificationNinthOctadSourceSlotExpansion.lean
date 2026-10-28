/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotGenericExpansion

/-! Checked original source-slot address certificates instantiate the exact sparse signed
coefficient identity. The complete six-field source-row family remains explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The checked original target, coverage and distinctness source-slot certificates. -/
def generatedNinthOctadSourceSlotCertificates : GeneratedNinthOctadSourceSlotCertificates :=
  ⟨generatedNinth_octad_source_slot_target, generatedNinth_octad_source_slot_coverage,
    generatedNinth_octad_source_slot_distinct⟩

/-- The original actual sparse coefficient identity with checked source-slot addresses. -/
theorem generatedNinth_middle_octad_sparse_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (o, e))) =
        (generatedNinthOctadSparseNumerator o e : ℝ) / 16 := by
  exact generatedNinth_middle_octad_sparse_of_slot_certificates
    generatedNinthOctadSourceSlotCertificates hcert o e

/-- The original actual sparse coefficient identity with checked source-slot addresses. -/
theorem generatedNinth_final_octad_sparse_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedNinthFinalOctadSparseNumerator o e : ℝ) / 128 := by
  exact generatedNinth_final_octad_sparse_of_slot_certificates
    generatedNinthOctadSourceSlotCertificates hcert o e

/-- The original actual sparse coefficient identity with checked source-slot addresses. -/
theorem generatedNinth_final_octad_slot_of_certificates
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedNinthFinalOctadSlotNumerator o e : ℝ) / 128 := by
  exact generatedNinth_final_octad_slot_of_slot_certificates
    generatedNinthOctadSourceSlotCertificates hcert o e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
