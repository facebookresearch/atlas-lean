/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagCubeLift

/-! Eleven actual conjugates of the proved cube sign span every equal-pair Golay sign code. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Code labels of eleven signed-code conjugates, checked against genuine permutations below. -/
def generatedFourthMonomialSignLabels : Fin 11 → Fin 4096 :=
  ![15, 4079, 1117, 1255, 2295, 3797, 2237, 3993, 3551, 632, 2173]

/-- Actual codewords at the eleven recorded coefficient labels. -/
def generatedFourthMonomialSignCode (j : Fin 11) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients (generatedFourthMonomialSignLabels j)),
    ⟨golayLabelCoefficients (generatedFourthMonomialSignLabels j), rfl⟩⟩

/-- The eleven literal conjugating words in the four genuine flag permutations. -/
def generatedFourthMonomialSignWitnessWord : Fin 11 → List (Fin 4) :=
  ![[], [0], [2], [1, 0], [2, 0], [3, 0], [0, 2], [1, 2], [3, 1, 0], [0, 2, 0], [1, 0, 2]]

/-- Genuine Golay permutations of the eleven codeword conjugating words. -/
def generatedFourthMonomialSignWitnessPermutation (j : Fin 11) : golayAutomorphismSubgroup :=
  ((generatedFourthMonomialSignWitnessWord j).map generatedFourthMonomialPermutation).prod

/-- Every stored codeword is the actual permuted cube codeword, not merely a binary label. -/
theorem generatedFourth_monomial_sign_witness : ∀ j : Fin 11,
    golayPermute (generatedFourthMonomialSignWitnessPermutation j).val
      generatedFourthFlagCubeSignCode.val = (generatedFourthMonomialSignCode j).val := by
  decide +kernel

/-- The actual relative pair-sign functional in encoder coordinates. -/
def generatedFourthMonomialRelativePhase : (Fin 12 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun a := golayEncoder a 8 + golayEncoder a 11
  map_add' a b := by simp only [map_add, Pi.add_apply]; abel
  map_smul' c a := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Linear combinations of the eleven actual encoder coefficient vectors. -/
def generatedFourthMonomialSignCoefficientMap :
    (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) where
  toFun a := ∑ j, a j • golayLabelCoefficients (generatedFourthMonomialSignLabels j)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

/-- A literal retraction onto the eleven-dimensional equal-pair coefficient space. -/
def generatedFourthMonomialSignRetractionMatrix : Matrix (Fin 11) (Fin 12) (ZMod 2) :=
  fun i j =>
    if Nat.testBit
      ((![461, 710, 745, 2853, 3055, 3276, 3462, 5, 963, 3087, 933] : Fin 11 → ℕ) i) j.val
    then 1 else 0

/-- The genuine F2 linear retraction given by the finite matrix. -/
def generatedFourthMonomialSignRetraction :
    (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) :=
  generatedFourthMonomialSignRetractionMatrix.mulVecLin

set_option maxHeartbeats 4000000 in
-- Check the twelve encoder basis vectors against the literal eleven-row retraction.
/-- Basis columns reconstruct each original vector with its relative phase removed. -/
theorem generatedFourth_monomial_sign_retraction_basis : ∀ i : Fin 12,
    generatedFourthMonomialSignCoefficientMap
      (generatedFourthMonomialSignRetraction (Pi.single i 1)) =
        Pi.single i 1 + generatedFourthMonomialRelativePhase (Pi.single i 1) • Pi.single 4 1 := by
  decide +kernel

/-- The checked basis certificate extends to every original encoder coefficient vector. -/
theorem generatedFourth_monomial_sign_retraction (a : Fin 12 → ZMod 2) :
    generatedFourthMonomialSignCoefficientMap (generatedFourthMonomialSignRetraction a) =
      a + generatedFourthMonomialRelativePhase a • Pi.single 4 1 := by
  have hl : generatedFourthMonomialSignCoefficientMap.comp generatedFourthMonomialSignRetraction =
      LinearMap.id + generatedFourthMonomialRelativePhase.smulRight (Pi.single 4 1) := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply] using
        generatedFourth_monomial_sign_retraction_basis i
  exact LinearMap.congr_fun hl a

/-- Equal-pair Golay codewords are combinations of the eleven genuine codeword conjugates. -/
theorem generatedFourth_monomial_equal_sign_span (c : golayCode) (hc : c.val 8 = c.val 11) :
    ∃ a : Fin 11 → ZMod 2, c.val = ∑ j, a j • (generatedFourthMonomialSignCode j).val := by
  obtain ⟨b, hb⟩ := c.property
  have hp : generatedFourthMonomialRelativePhase b = 0 := by
    change golayEncoder b 8 + golayEncoder b 11 = 0
    rw [hb, hc, CharTwo.add_self_eq_zero]
  refine ⟨generatedFourthMonomialSignRetraction b, ?_⟩
  have he := generatedFourth_monomial_sign_retraction b
  rw [hp, zero_smul, add_zero] at he
  calc
    c.val = golayEncoder b := hb.symm
    _ = golayEncoder (generatedFourthMonomialSignCoefficientMap
        (generatedFourthMonomialSignRetraction b)) := congrArg golayEncoder he.symm
    _ = ∑ j, generatedFourthMonomialSignRetraction b j •
        (generatedFourthMonomialSignCode j).val := by
      change golayEncoder (∑ j, generatedFourthMonomialSignRetraction b j •
        golayLabelCoefficients (generatedFourthMonomialSignLabels j)) = _
      simp only [map_sum, map_smul, generatedFourthMonomialSignCode]


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
