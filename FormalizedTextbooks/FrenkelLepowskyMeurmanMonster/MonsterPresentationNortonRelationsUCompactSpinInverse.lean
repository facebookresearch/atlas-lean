/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- One exact sixty-four-term numerator for the inverse of the actual Norton spin factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem diagonal_inv (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M)⁻¹ = monsterMonomialDiagonalHolomorph M := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

private theorem permutation_inv (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph P)⁻¹ = monsterMonomialPermutationHolomorph P.symm := by
  apply Subtype.ext
  exact (monsterMonomialPermutation_symm P).symm

private theorem gaussian_inv : xiSpinGHolomorph⁻¹ = xiSpinGHolomorph := by
  apply Subtype.ext
  exact inv_eq_of_mul_eq_one_right xiSpinGEquiv_square

private theorem inverse_word (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (spinHolomorphIncl q * monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P * xiSpinGHolomorph *
        monsterMonomialPermutationHolomorph R * monsterMonomialDiagonalHolomorph N)⁻¹ =
    monsterMonomialDiagonalHolomorph N * monsterMonomialPermutationHolomorph R.symm *
      xiSpinGHolomorph * monsterMonomialPermutationHolomorph P.symm *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q⁻¹ := by
  simp only [mul_inv_rev, diagonal_inv, permutation_inv, gaussian_inv, ← map_inv, mul_assoc]

/-- The inverse compact word contains the same single actual Gaussian. -/
noncomputable def monsterNortonUCompactInverseSpin : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 1) *
    monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 1).symm *
      xiSpinGHolomorph *
        monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 0).symm *
          monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 0) *
            spinHolomorphIncl monsterNortonUCompactCorrection⁻¹

/-- This genuine compact word is the group inverse of the original candidate. -/
theorem monsterNortonUCompactInverseSpin_eq :
    monsterNortonUCompactSpin⁻¹ = monsterNortonUCompactInverseSpin :=
  inverse_word _ _ _ _ _

/-- The integral inverse numerator retains the full inner Q correction and one Gaussian sum. -/
def monsterNortonUCompactInverseNumerator (v : NortonUIntegerVector) : NortonUIntegerVector :=
  monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 1)
    (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 1).symm
      (nortonUIntegerG
        (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0).symm
          (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
            (nortonUIntegerQ monsterNortonUCompactCorrection⁻¹ v)))))

private theorem diagonal_embed (M : Fin 12 → Fin 12 → ZMod 2)
    (v : NortonUIntegerVector) :
    monsterMonomialDiagonalEquiv M (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (monsterNortonUCompactIntegerDiagonal M v) := by
  ext t
  change qSign (monsterMonomialQuadratic M t) * (v (nortonUIntegerLabel t) : ℝ) = _
  simp only [nortonUIntegerEmbed, monsterNortonUCompactIntegerDiagonal,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

private theorem permutation_embed (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (v : NortonUIntegerVector) :
    monsterMonomialPermutation P (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (monsterNortonUCompactIntegerPermutation P v) := by
  ext t
  simp only [monsterMonomialPermutation_apply, nortonUIntegerEmbed,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse]

private theorem inverse_six_factor_embed (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (v : NortonUIntegerVector) :
    (monsterMonomialDiagonalHolomorph N * monsterMonomialPermutationHolomorph R.symm *
      xiSpinGHolomorph * monsterMonomialPermutationHolomorph P.symm *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q⁻¹).val
      (nortonUIntegerEmbed v) =
    (1 / 8 : ℝ) • nortonUIntegerEmbed
      (monsterNortonUCompactIntegerDiagonal N (monsterNortonUCompactIntegerPermutation R.symm
        (nortonUIntegerG (monsterNortonUCompactIntegerPermutation P.symm
          (monsterNortonUCompactIntegerDiagonal M (nortonUIntegerQ q⁻¹ v)))))) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change monsterMonomialDiagonalEquiv N (monsterMonomialPermutation R.symm
    (xiSpinG (monsterMonomialPermutation P.symm (monsterMonomialDiagonalEquiv M
      (spinRepresentation q⁻¹ (nortonUIntegerEmbed v)))))) = _
  simp only [nortonUIntegerQ_embed, diagonal_embed, permutation_embed,
    nortonUIntegerG_embed, map_smul]

/-- The compact inverse numerator embeds as its actual real spin operator. -/
theorem monsterNortonUCompactInverseNumerator_embed (v : NortonUIntegerVector) :
    monsterNortonUCompactInverseSpin.val (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator v) :=
  inverse_six_factor_embed _ _ _ _ _ v

private theorem negative_inverse (a b : SpinHolomorph)
    (h : ∀ x : SpinSpace, a.val x = -b.val x) (x : SpinSpace) :
    (a⁻¹).val x = -(b⁻¹).val x := by
  apply a.val.injective
  change a.val (a.val.symm x) = a.val (-b.val.symm x)
  rw [LinearEquiv.apply_symm_apply, map_neg, h, neg_neg, LinearEquiv.apply_symm_apply]

/-- Every actual inverse Norton spin action is the negative of this genuine compact inverse. -/
theorem monsterNortonUCompactInverseSpin_actual_apply (x : SpinSpace) :
    (monsterNortonUFiber.val.1⁻¹).val x = -monsterNortonUCompactInverseSpin.val x := by
  rw [← monsterNortonUCompactInverseSpin_eq]
  exact negative_inverse _ _ monsterNortonUCompactSpin_actual_apply x

/-- Actual inverse Norton spin action has its exact one-Gaussian integer numerator. -/
theorem monsterNortonUCompactInverseSpin_actual_embed (v : NortonUIntegerVector) :
    (monsterNortonUFiber.val.1⁻¹).val (nortonUIntegerEmbed v) =
      (-1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator v) := by
  rw [monsterNortonUCompactInverseSpin_actual_apply, monsterNortonUCompactInverseNumerator_embed]
  rw [← neg_smul]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
