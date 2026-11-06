/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- One exact sixteen-term numerator for the inverse of the actual Norton spin factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinActual

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

private theorem gaussian_inv : monsterNortonUTwoGaussianHolomorph⁻¹ =
  monsterNortonUTwoGaussianHolomorph := by
  apply Subtype.ext
  apply inv_eq_of_mul_eq_one_right
  apply LinearEquiv.ext
  intro f
  exact congrArg (fun T : SpinSpace →ₗ[ℝ] SpinSpace => T f)
    monsterNortonUTwoGaussian_square

private theorem inverse_word (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (spinHolomorphIncl q * monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P * monsterNortonUTwoGaussianHolomorph *
        monsterMonomialPermutationHolomorph R * monsterMonomialDiagonalHolomorph N)⁻¹ =
    monsterMonomialDiagonalHolomorph N * monsterMonomialPermutationHolomorph R.symm *
      monsterNortonUTwoGaussianHolomorph * monsterMonomialPermutationHolomorph P.symm *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q⁻¹ := by
  simp only [mul_inv_rev, diagonal_inv, permutation_inv, gaussian_inv, ← map_inv, mul_assoc]

/-- The inverse compact word contains the same single actual Gaussian. -/
noncomputable def monsterNortonUTwoCompactInverseSpin : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 1) *
    monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 1).symm *
      monsterNortonUTwoGaussianHolomorph *
        monsterMonomialPermutationHolomorph (monsterNortonUTwoCompactPermutation 0).symm *
          monsterMonomialDiagonalHolomorph (monsterNortonUTwoCompactDiagonal 0) *
            spinHolomorphIncl monsterNortonUTwoCompactCorrection⁻¹

/-- This genuine compact word is the group inverse of the original candidate. -/
theorem monsterNortonUTwoCompactInverseSpin_eq :
    monsterNortonUTwoCompactSpin⁻¹ = monsterNortonUTwoCompactInverseSpin :=
  inverse_word _ _ _ _ _

/-- The integral inverse numerator retains the full inner Q correction and one Gaussian sum. -/
def monsterNortonUTwoCompactInverseNumerator (v : NortonUIntegerVector) : NortonUIntegerVector :=
  monsterNortonUCompactIntegerDiagonal (monsterNortonUTwoCompactDiagonal 1)
    (monsterNortonUCompactIntegerPermutation (monsterNortonUTwoCompactPermutation 1).symm
      (monsterNortonUTwoGaussianInteger
        (monsterNortonUCompactIntegerPermutation (monsterNortonUTwoCompactPermutation 0).symm
          (monsterNortonUCompactIntegerDiagonal (monsterNortonUTwoCompactDiagonal 0)
            (nortonUIntegerQ monsterNortonUTwoCompactCorrection⁻¹ v)))))

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
      monsterNortonUTwoGaussianHolomorph * monsterMonomialPermutationHolomorph P.symm *
        monsterMonomialDiagonalHolomorph M * spinHolomorphIncl q⁻¹).val
      (nortonUIntegerEmbed v) =
    (1 / 4 : ℝ) • nortonUIntegerEmbed
      (monsterNortonUCompactIntegerDiagonal N (monsterNortonUCompactIntegerPermutation R.symm
        (monsterNortonUTwoGaussianInteger (monsterNortonUCompactIntegerPermutation P.symm
          (monsterNortonUCompactIntegerDiagonal M (nortonUIntegerQ q⁻¹ v)))))) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change monsterMonomialDiagonalEquiv N (monsterMonomialPermutation R.symm
    (monsterNortonUTwoGaussian (monsterMonomialPermutation P.symm (monsterMonomialDiagonalEquiv M
      (spinRepresentation q⁻¹ (nortonUIntegerEmbed v)))))) = _
  simp only [nortonUIntegerQ_embed, diagonal_embed, permutation_embed,
    monsterNortonUTwoGaussianInteger_embed, map_smul]

/-- The compact inverse numerator embeds as its actual real spin operator. -/
theorem monsterNortonUTwoCompactInverseNumerator_embed (v : NortonUIntegerVector) :
    monsterNortonUTwoCompactInverseSpin.val (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactInverseNumerator v) :=
  inverse_six_factor_embed _ _ _ _ _ v

/-- The inverse squared Norton spin action has the same actual sixteen-term Gaussian. -/
theorem monsterNortonUTwoCompactInverseSpin_actual_embed (v : NortonUIntegerVector) :
    ((monsterNortonUFiber.val.1 ^ 2)⁻¹).val (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactInverseNumerator v) := by
  rw [monsterNortonUTwoCompactSpin_actual, monsterNortonUTwoCompactInverseSpin_eq]
  exact monsterNortonUTwoCompactInverseNumerator_embed v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
