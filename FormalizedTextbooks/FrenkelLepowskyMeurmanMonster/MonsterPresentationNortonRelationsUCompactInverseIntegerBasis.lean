/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer basis expansions of the actual inverse Norton compact numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactInverseSpinBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegerBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem eighth_sign (x y : ℝ)
    (h : (1 / 8 : ℝ) * x = (-1 / 8 : ℝ) * y) : y = -x := by
  linarith

/-- Each actual inverse integer basis image is a signed sum of sixty-four compact transitions. -/
theorem monsterNortonUCompactInverseNumerator_basis (u : Fin 4096) :
    monsterNortonUCompactInverseNumerator (Pi.single u 1) =
      -(∑ a : XiGrayIndex, monsterNortonUCompactInverseBasisSign (golayLabelCoefficients u) a •
        (Pi.single (nortonUIntegerLabel
          (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients u) a)) 1 :
            NortonUIntegerVector)) := by
  funext n
  apply Int.cast_injective (α := ℝ)
  have hi : Function.Injective nortonUIntegerLabel :=
    Function.LeftInverse.injective nortonUIntegerLabel_inverse
  have hs := monsterNortonUCompactInverseSpin_actual_embed (Pi.single u 1)
  have hn := congrFun hs (golayLabelCoefficients n)
  conv_lhs at hn =>
    rw [monsterNortonUIntegerEmbed_single, monsterNortonUCompactInverseSpin_actual_basis]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff] at hn
  have he (a : XiGrayIndex) : n = nortonUIntegerLabel
      (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients u) a) ↔
      golayLabelCoefficients n =
        monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients u) a := by
    constructor
    · intro h
      rw [h, nortonUIntegerLabel_inverse]
    · intro h
      have hh := congrArg nortonUIntegerLabel h
      rwa [nortonUIntegerLabel_coeff] at hh
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_neg, Int.cast_sum, Int.cast_mul, Pi.single_apply, he,
    Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp only [Pi.single_apply] at hn
  exact eighth_sign _ _ hn

/-- The same integer basis expansion uses the genuine published 64-term enumeration. -/
theorem monsterNortonUCompactInverseNumerator_basis_fin64 (u : Fin 4096) :
    monsterNortonUCompactInverseNumerator (Pi.single u 1) =
      -(∑ a : Fin 64,
        monsterNortonUCompactInverseBasisSign (golayLabelCoefficients u)
          (monsterNortonGrayCoefficients a) •
        (Pi.single (nortonUIntegerLabel
          (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients u)
            (monsterNortonGrayCoefficients a))) 1 : NortonUIntegerVector)) := by
  rw [monsterNortonUCompactInverseNumerator_basis]
  apply congrArg (fun v : NortonUIntegerVector => -v)
  exact (Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    monsterNortonUCompactInverseBasisSign (golayLabelCoefficients u) a •
      (Pi.single (nortonUIntegerLabel
        (monsterNortonUCompactInverseBasisIndex (golayLabelCoefficients u) a)) 1 :
          NortonUIntegerVector))).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
