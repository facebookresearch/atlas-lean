/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinProfiles
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialSourceAction

/-! The complete signed C certificate gives its actual Q automorphism by finite coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
-- Verify both original twelve-coordinate transporter matrices, before using their inverse.
/-- The original C coordinate rows and original inverse-C rows are mutual inverses. -/
theorem generatedSixth_C_coordinate_inverse :
    representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) *
      representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1) = 1 ∧
    representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1) *
      representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) = 1 := by
  decide +kernel

/-- The translation equivalence inverse to the original C spin-coordinate pullback. -/
def generatedSixthCTranslation : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun a := representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1) *ᵥ a
  invFun a := representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) *ᵥ a
  left_inv a := by
    change representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) *ᵥ
      (representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, generatedSixth_C_coordinate_inverse.1, Matrix.one_mulVec]
  right_inv a := by
    change representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1) *ᵥ
      (representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, generatedSixth_C_coordinate_inverse.2, Matrix.one_mulVec]
  map_add' _ _ := Matrix.mulVec_add _ _ _
  map_smul' _ _ := Matrix.mulVec_smul _ _ _

/-- The finite monomial C image retains its actual central phase and modulation shear. -/
def generatedSixthCImage (q : Q) : Q :=
  monsterMonomialDiagonalImage
    (fun i j => representativeMatrix (generatedSixthPermutationProfilePhaseRows 1) i j)
    (monsterMonomialPermutationImage generatedSixthCTranslation q)

/-- A full signed coordinate certificate determines the entire genuine Q automorphism. -/
theorem generatedSixth_spin_conjugation_of_monomial (g : SpinHolomorph)
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (M : Fin 12 → Fin 12 → ZMod 2)
    (hg : ∀ f : SpinSpace, ∀ t : SpinIndex,
      g.val f t = qSign (monsterMonomialQuadratic M t) * f (P.symm t)) (q : Q) :
    spinConjugation g q =
      monsterMonomialDiagonalImage M (monsterMonomialPermutationImage P q) := by
  have he : g = monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro f
    funext t
    rw [hg]
    rfl
  rw [he, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph M)
    (spinConjugation (monsterMonomialPermutationHolomorph P) q) = _
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]

set_option maxHeartbeats 2000000 in
-- Retain the complete original signed holomorph while identifying its finite Q automorphism.
/-- The original C action on every genuine Q element is the complete finite monomial formula. -/
theorem generatedSixth_C_conjugation (q : Q) :
    spinConjugation leechRootedA2SixthXiTransportFiber.val.1 q =
      generatedSixthCImage q := by
  apply generatedSixth_spin_conjugation_of_monomial _ generatedSixthCTranslation _ _ q
  exact generatedSixth_permutation_profile_spin 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
