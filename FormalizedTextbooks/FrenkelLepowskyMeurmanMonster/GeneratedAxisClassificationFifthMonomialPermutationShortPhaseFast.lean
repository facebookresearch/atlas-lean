/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignPhysicalCharacter

/-! The original monomial polynomial is independent of the all-one spin bit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem quadratic_omega (M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hM : ∀ i, M i 11 = 0 ∧ M 11 i = 0) (x : SpinIndex) (b : ZMod 2) :
    monsterMonomialQuadratic M (x + b • Pi.single 11 1) = monsterMonomialQuadratic M x := by
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · simp only [zero_smul, add_zero]
  · rw [one_smul, monsterMonomialQuadratic_add, representativeQuadratic_single, (hM 11).1,
      add_zero]
    have hz' : monsterMonomialGradient M x 11 = 0 := by
      unfold monsterMonomialGradient
      apply Finset.sum_eq_zero
      intro i _
      rw [(hM i).1, (hM i).2, add_zero, mul_zero]
    have hz : spinDot (monsterMonomialGradient M x) (Pi.single 11 1) = 0 := by
      simpa [spinDot, Pi.single_apply, mul_ite] using hz'
    rw [hz, add_zero]

/-- The final literal phase models have no original all-one coefficient. -/
theorem generatedFifth_permutation_phase_omega_coefficients : ∀ k : Fin 6, ∀ i : Fin 12,
    (generatedFifthMonomialPermutationSpinModel k).phase i 11 = 0 ∧
      (generatedFifthMonomialPermutationSpinModel k).phase 11 i = 0 := by
  decide +kernel

/-- The full original Parker phase is constant across the two all-one addresses. -/
theorem generatedFifth_permutation_phase_omega (k : Fin 6) (x : SpinIndex) (b : ZMod 2) :
    generatedFifthMonomialPermutationModelPhase k (x + b • Pi.single 11 1) =
      generatedFifthMonomialPermutationModelPhase k x :=
  quadratic_omega _ (generatedFifth_permutation_phase_omega_coefficients k) x b

/-- Each actual correcting modulation annihilates the all-one address. -/
theorem generatedFifth_permutation_correction_omega : ∀ k : Fin 6,
    spinDot (spinModulation (generatedFifthMonomialPermutationCorrection k))
      (Pi.single 11 1) = 0 := by
  decide +kernel

/-- The full original short phase is its family constant plus the actual physical character. -/
theorem generatedFifth_permutation_short_phase_formula (k : Fin 6) (j : Fin 56) (e : Fin 64) :
    generatedFifthMonomialPermutationShortPhase k (Sum.inr (j, e)) =
      generatedFifthMonomialPermutationModelPhase k
          (golayLabelCoefficients (generatedFifthEvenRootCode j)) +
        generatedFifthSignFamilyConstant (generatedFifthMonomialPermutationTranslation k)
          (golayLabelCoefficients (generatedFifthMonomialPermutationModulation k)) j +
        generatedFifthSignNegativeCharacter
          (generatedFifthMonomialPermutationTranslation k) j e := by
  rw [generatedFifthMonomialPermutationShortPhase]
  have ha : spinTranslation (generatedFifthMonomialPermutationCorrection k) =
      golayLabelCoefficients (generatedFifthMonomialPermutationTranslation k) :=
    generatedAxisFourthQFromSpin_translation _ _ _
  rw [generatedFifth_sign_short_phase_formula (generatedFifthMonomialPermutationCorrection k)
    (generatedFifthMonomialPermutationTranslation k) ha
    (generatedFifth_permutation_correction_omega k) j e]
  simp only [generatedFifthXiShortCachedQ, generatedAxisFourthQFromSpin_translation]
  rw [generatedFifth_permutation_phase_omega]
  simp only [generatedFifthMonomialPermutationCorrection, generatedAxisFourthQFromSpin_modulation]
  exact (add_assoc _ _ _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
