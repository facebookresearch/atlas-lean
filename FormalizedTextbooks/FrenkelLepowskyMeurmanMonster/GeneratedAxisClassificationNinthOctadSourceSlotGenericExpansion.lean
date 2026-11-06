/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowGenericExpansion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOctadTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! The sparse source slots recover actual octad coefficients from the original complete
six-field row-certificate family. The complete family remains a separate prerequisite. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Exactly the original three universal source-slot address certificate properties. -/
structure GeneratedNinthOctadSourceSlotCertificates : Prop where
  /-- Every nonempty slot has a nonzero source and its original octad target descriptor. -/
  target : ∀ (o : Fin 759) (j : Fin 8), generatedNinthOctadSourceSlotWord o j ≠ 0 →
    generatedNinthShortRowNonzero (generatedNinthOctadSourceSlotIndex o j) = true ∧
      generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) =
        Sum.inr (Sum.inl (o, generatedNinthOctadSourceSlotSign o j))
  /-- Every nonzero source with an octad descriptor occurs at its original octad and sign. -/
  coverage : ∀ k : Fin 4136, generatedNinthShortRowNonzero k = true →
    match generatedNinthShortRowTarget k with
    | Sum.inr (Sum.inl (o, e)) => ∃ j : Fin 8,
        generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
          generatedNinthOctadSourceSlotIndex o j = k ∧ generatedNinthOctadSourceSlotSign o j = e
    | _ => True
  /-- Nonempty source indices are distinct within each original octad's slots. -/
  distinct : ∀ (o : Fin 759) (j l : Fin 8), generatedNinthOctadSourceSlotWord o j ≠ 0 →
    generatedNinthOctadSourceSlotWord o l ≠ 0 →
      generatedNinthOctadSourceSlotIndex o j = generatedNinthOctadSourceSlotIndex o l → j = l

/-- Integer middle octad numerator from at most eight actual source addresses and full phases. -/
def generatedNinthOctadSparseNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ j : Fin 8, if generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
      generatedNinthOctadSourceSlotSign o j = e then
    nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
      generatedNinthOriginalShortNumerator
        (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) else 0

/-- The sparse signed source sum gives every actual middle octad coordinate over16. -/
theorem generatedNinth_middle_octad_sparse_of_slot_certificates
    (hslot : GeneratedNinthOctadSourceSlotCertificates)
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (o, e))) =
        (generatedNinthOctadSparseNumerator o e : ℝ) / 16 := by
  classical
  let r : GriessShortIndex := Sum.inr (Sum.inl (o, e))
  let c (j : Fin 8) : Prop := generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
    generatedNinthOctadSourceSlotSign o j = e
  have ht (j : Fin 8) (hj : c j) :
      generatedNinthShortRowTarget (generatedNinthOctadSourceSlotIndex o j) = r := by
    simpa only [hj.2] using (hslot.target o j hj.1).2
  have hsum : (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
        generatedFifthAxis)).2.1 r = ∑ j : Fin 8, if c j then
      qSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        ((generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j)) : ℝ) / 16)
      else 0 := by
    by_cases h : ∃ j : Fin 8, c j
    · obtain ⟨j, hj⟩ := h
      rw [Finset.sum_eq_single j]
      · simpa only [hj, ite_true, ht j hj] using
          generatedNinth_short_row_coefficient_actual
            (generatedNinthOctadSourceSlotIndex o j)
            (hcert (generatedNinthOctadSourceSlotIndex o j))
      · intro l _ hlj
        have hl : ¬ c l := by
          intro hl
          have hk := generatedNinth_short_row_target_injective_of_certificates hcert
            ((ht l hl).trans (ht j hj).symm)
          exact hlj (hslot.distinct o l j hl.1 hj.1 hk)
        simp only [hl, ite_false]
      · simp
    · have hz : (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
          generatedFifthAxis)).2.1 r = 0 := by
        apply not_ne_iff.mp
        intro hn
        obtain ⟨k, hk, hkn⟩ :=
          generatedNinth_short_row_nonzero_covered_of_certificates hcert r hn
        have hc := hslot.coverage k
          ((generatedNinth_short_row_nonzero_actual k).mpr hkn)
        rw [hk] at hc
        obtain ⟨j, hj, _, hje⟩ := hc
        exact h ⟨j, hj, hje⟩
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hj : ¬ c j := fun hj => h ⟨j, hj⟩
      simp only [hj, ite_false]
  unfold generatedNinthOctadSparseNumerator
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_zero, nortonUIntegerSign_real]
  rw [Finset.sum_div]
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [c]
  by_cases hj : generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
      generatedNinthOctadSourceSlotSign o j = e
  · simp only [ite_eq_left hj]
    ring
  · simp only [ite_eq_right hj, zero_div]

/-- Exact final octad integer numerator from the original signed Fourier matrix. -/
def generatedNinthFinalOctadSparseNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ f : Fin 64, trialityIntegerMatrix e f * generatedNinthOctadSparseNumerator o f

/-- Every actual final octad coefficient is the full-phase sparse Fourier numerator over128. -/
theorem generatedNinth_final_octad_sparse_of_slot_certificates
    (hslot : GeneratedNinthOctadSourceSlotCertificates)
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedNinthFinalOctadSparseNumerator o e : ℝ) / 128 := by
  rw [generatedNinthAxis_local_expression]
  exact generatedNinth_final_triality_octad_integer _ o
    (generatedNinthOctadSparseNumerator o)
    (generatedNinth_middle_octad_sparse_of_slot_certificates hslot hcert o) e

/-- The same full signed Fourier numerator with one term per original nonempty source slot. -/
def generatedNinthFinalOctadSlotNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ j : Fin 8, if generatedNinthOctadSourceSlotWord o j ≠ 0 then
    trialityIntegerMatrix e (generatedNinthOctadSourceSlotSign o j) *
      (nortonUIntegerSign (generatedNinthShortRowPhase (generatedNinthOctadSourceSlotIndex o j)) *
        generatedNinthOriginalShortNumerator
          (generatedNinthShortRowSource (generatedNinthOctadSourceSlotIndex o j))) else 0

/-- Exchanging the finite Fourier and sparse source sums yields the eight-slot formula. -/
theorem generatedNinth_final_octad_slot_numerator_eq (o : Fin 759) (e : Fin 64) :
    generatedNinthFinalOctadSparseNumerator o e = generatedNinthFinalOctadSlotNumerator o e := by
  classical
  unfold generatedNinthFinalOctadSparseNumerator generatedNinthOctadSparseNumerator
    generatedNinthFinalOctadSlotNumerator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : generatedNinthOctadSourceSlotWord o j ≠ 0
  · rw [Finset.sum_eq_single (generatedNinthOctadSourceSlotSign o j)]
    · simp only [and_true, ite_eq_left hj]
    · intro f _ hf
      have hne : generatedNinthOctadSourceSlotSign o j ≠ f := Ne.symm hf
      have hn : ¬ (generatedNinthOctadSourceSlotWord o j ≠ 0 ∧
          generatedNinthOctadSourceSlotSign o j = f) := fun h => hne h.2
      simp only [ite_eq_right hn, mul_zero]
    · simp
  · simp only [hj, false_and, ite_false, mul_zero, Finset.sum_const_zero]

/-- The exact final octad coefficient can be evaluated with the eight original source slots. -/
theorem generatedNinth_final_octad_slot_of_slot_certificates
    (hslot : GeneratedNinthOctadSourceSlotCertificates)
    (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedNinthFinalOctadSlotNumerator o e : ℝ) / 128 := by
  rw [← generatedNinth_final_octad_slot_numerator_eq]
  exact generatedNinth_final_octad_sparse_of_slot_certificates hslot hcert o e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
