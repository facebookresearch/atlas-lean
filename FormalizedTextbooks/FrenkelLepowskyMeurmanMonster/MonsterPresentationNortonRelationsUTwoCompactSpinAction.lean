/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An exact one-Gaussian integer numerator for the genuine compact spin factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

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

/-- The exact integral numerator of the compact actual operator, with denominator four. -/
def monsterNortonUTwoCompactNumerator (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerQ monsterNortonUTwoCompactCorrection
    (monsterNortonUCompactIntegerDiagonal (monsterNortonUTwoCompactDiagonal 0)
      (monsterNortonUCompactIntegerPermutation (monsterNortonUTwoCompactPermutation 0)
        (monsterNortonUTwoGaussianInteger
          (monsterNortonUCompactIntegerPermutation (monsterNortonUTwoCompactPermutation 1)
            (monsterNortonUCompactIntegerDiagonal (monsterNortonUTwoCompactDiagonal 1) v)))))

private theorem six_factor_embed (q : Q) (M N : Fin 12 → Fin 12 → ZMod 2)
    (P R : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (v : NortonUIntegerVector) :
    (spinHolomorphIncl q * monsterMonomialDiagonalHolomorph M *
      monsterMonomialPermutationHolomorph P * monsterNortonUTwoGaussianHolomorph *
        monsterMonomialPermutationHolomorph R * monsterMonomialDiagonalHolomorph N).val
      (nortonUIntegerEmbed v) =
    (1 / 4 : ℝ) • nortonUIntegerEmbed
      (nortonUIntegerQ q (monsterNortonUCompactIntegerDiagonal M
        (monsterNortonUCompactIntegerPermutation P (monsterNortonUTwoGaussianInteger
          (monsterNortonUCompactIntegerPermutation R
            (monsterNortonUCompactIntegerDiagonal N v)))))) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change spinRepresentation q (monsterMonomialDiagonalEquiv M
    (monsterMonomialPermutation P (monsterNortonUTwoGaussian
      (monsterMonomialPermutation R (monsterMonomialDiagonalEquiv N
        (nortonUIntegerEmbed v)))))) = _
  simp only [diagonal_embed, permutation_embed, monsterNortonUTwoGaussianInteger_embed,
    map_smul, nortonUIntegerQ_embed]

/-- This sixteen-term integer formula is the actual compact spin operator on real vectors. -/
theorem monsterNortonUTwoCompactNumerator_embed (v : NortonUIntegerVector) :
    monsterNortonUTwoCompactSpin.val (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactNumerator v) :=
  six_factor_embed _ _ _ _ _ v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
