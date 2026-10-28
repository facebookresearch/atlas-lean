/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQCandidate

/-! Exact actual Q subgroup fixing all original tensor columns of the fifth prototype. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- The actual extraspecial subgroup fixing every original fifth tensor column. -/
def generatedFifthTensorQStabilizer : Subgroup Q where
  carrier := {q | ∀ i : Fin 24, spinRepresentation q
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i)}
  one_mem' := by intro i; simp
  mul_mem' := by
    intro q r hq hr i
    rw [map_mul, LinearEquiv.mul_apply, hr i, hq i]
  inv_mem' := by
    intro q hq i
    have h := congrArg (spinRepresentation q⁻¹) (hq i)
    simpa only [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      LinearEquiv.coe_one, id_eq] using h.symm

/-- Every actual fixing Pauli element is one of the 32 literal phase-corrected candidates. -/
theorem generatedFifth_tensor_Q_mem_iff (q : Q) :
    q ∈ generatedFifthTensorQStabilizer ↔
      ∃ b : ZMod 2, ∃ k : Fin 16, generatedFifthQCandidate b k = q := by
  constructor
  · intro hq
    have ht := generatedFifth_tensor_translation q hq
    obtain ⟨b, hb⟩ : ∃ b : ZMod 2,
        spinTranslation q = b • (Pi.single 11 1 : SpinIndex) := by
      rcases ht with ht | ht
      · exact ⟨0, by simpa only [zero_smul] using ht⟩
      · exact ⟨1, by simpa only [one_smul] using ht⟩
    obtain ⟨m, hm⟩ := golayLabelCoefficients_bijective.2 (spinModulation q)
    have hmc : (golayLabelCoefficients m) 11 = 0 ∧ ∀ j : Fin 64,
        spinDot (golayLabelCoefficients m)
          (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
            generatedFifthSpinLow (generatedFifthColumnLabels 0)) = 0 := by
      rw [hm]
      exact ⟨generatedFifth_tensor_modulation_omega q hq,
        generatedFifth_tensor_modulation_differences q hq⟩
    obtain ⟨k, hk⟩ := (generatedFifth_modulation_certificate m).mp hmc
    have hmod : golayLabelCoefficients (generatedFifthModulationLabels k) =
        spinModulation q := by rw [hk]; exact hm
    have hp : ∀ t : SpinIndex,
        (griessConwayEncode generatedFifthAxis).2.2 (t + spinTranslation q)
            (generatedFifthOddRootOutputData 0).2 =
          qSign b * (griessConwayEncode generatedFifthAxis).2.2 t
            (generatedFifthOddRootOutputData 0).2 := by
      have hb01 : b = 0 ∨ b = 1 := by fin_cases b <;> simp
      rcases hb01 with rfl | rfl
      · simp only [hb, zero_smul, add_zero, qSign_zero, one_mul, implies_true]
      · simp only [hb, one_smul, generatedFifth_tensor_add_omega,
          qSign_one, neg_one_mul, implies_true]
    have hc := generatedSpinSupport_fixed_phase q
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t
        (generatedFifthOddRootOutputData 0).2) b (hq _) hp _
          (generatedFifth_tensor_low_nonzero 0)
    change toAdd q.coeff + spinDot (spinModulation q)
      (generatedFifthSpinLow (generatedFifthColumnLabels 0)) + b = 0 at hc
    have hcoeff : toAdd q.coeff = spinDot (spinModulation q)
        (generatedFifthSpinLow (generatedFifthColumnLabels 0)) + b := by
      linear_combination hc -
        ZModModule.add_self (spinDot (spinModulation q)
          (generatedFifthSpinLow (generatedFifthColumnLabels 0))) - ZModModule.add_self b
    refine ⟨b, k, ?_⟩
    apply generatedAxisFourthQ_spin_coordinates_injective
    · exact (generatedAxisFourthQFromSpin_translation _ _ _).trans hb.symm
    · exact (generatedAxisFourthQFromSpin_modulation _ _ _).trans hmod
    · change spinDot (golayLabelCoefficients (generatedFifthModulationLabels k))
        (generatedFifthSpinLow (generatedFifthColumnLabels 0)) + b = toAdd q.coeff
      rw [hmod]
      exact hcoeff.symm
  · rintro ⟨b, k, rfl⟩
    exact generatedFifth_candidate_tensor_fixed b k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
