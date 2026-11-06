/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneFiber

/-! Whole preferred-Q conjugation of the genuine corrected Xi lift, with all central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The inverse compact word applies the inverse label map before the same quadratic sign. -/
def generatedSeventhXiPlaneCompactInverseImage (q : Q) : Q :=
  monsterMonomialDiagonalImage generatedSeventhXiPlanePhase
    (monsterMonomialPermutationImage generatedSeventhXiPlaneCode.symm q)

private theorem diagonal_inverse (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M)⁻¹ = monsterMonomialDiagonalHolomorph M := by
  apply Subtype.ext
  change (monsterMonomialDiagonalEquiv M)⁻¹ = monsterMonomialDiagonalEquiv M
  apply inv_eq_of_mul_eq_one_right
  apply LinearEquiv.ext
  exact monsterMonomialDiagonal_involutive M

private theorem permutation_inverse (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph P)⁻¹ = monsterMonomialPermutationHolomorph P.symm := by
  apply Subtype.ext
  exact (monsterMonomialPermutation_symm P).symm

/-- The explicit compact inverse includes the original coefficient, not just its binary image. -/
theorem generatedSeventhXiPlane_compact_inverse_conjugation (q : Q) :
    spinConjugation generatedSeventhXiPlaneCompactSpin⁻¹ q =
      generatedSeventhXiPlaneCompactInverseImage q := by
  rw [generatedSeventhXiPlaneCompactSpin, mul_inv_rev, diagonal_inverse,
    permutation_inverse, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph generatedSeventhXiPlanePhase)
      (spinConjugation (monsterMonomialPermutationHolomorph generatedSeventhXiPlaneCode.symm) q) = _
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]
  rfl

/-- The corrected action retains both original Gaussian images and actual Q conjugation. -/
def generatedSeventhXiPlaneQImage (q : Q) : Q :=
  generatedSeventhXiPlaneCorrection *
    generatedSeventhXiPlaneCompactImage
      (xiSpinGImage (xiSpinGammaImage (generatedSeventhXiPlaneCompactInverseImage q))) *
        generatedSeventhXiPlaneCorrection⁻¹

/-- Every original Q element, including its central phase, has this genuine corrected Xi image. -/
theorem generatedSeventhXiPlaneQImage_actual (q : Q) :
    spinConjugation generatedSeventhXiPlaneFiber.val.1 q =
      generatedSeventhXiPlaneQImage q := by
  rw [generatedSeventhXiPlaneFiber_spin, map_mul, map_mul, map_mul, map_inv]
  change spinConjugation (spinHolomorphIncl generatedSeventhXiPlaneCorrection)
    (spinConjugation generatedSeventhXiPlaneCompactSpin
      (spinConjugation xiSpinHolomorph
        (spinConjugation generatedSeventhXiPlaneCompactSpin⁻¹ q))) = _
  rw [generatedSeventhXiPlane_compact_inverse_conjugation,
    xiSpinHolomorph_conjugation, generatedSeventhXiPlaneCompactSpin_conjugation,
    spinConjugation_incl]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
