/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual compact integer numerator has its proved 64-term basis expansion. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinBasis
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The integer embedding preserves the genuine individual spin delta vectors. -/
theorem monsterNortonUIntegerEmbed_single (u : Fin 4096) :
    nortonUIntegerEmbed (Pi.single u 1) = Pi.single (golayLabelCoefficients u) 1 := by
  funext t
  have he : nortonUIntegerLabel t = u ↔ t = golayLabelCoefficients u := by
    constructor
    · intro h
      rw [← nortonUIntegerLabel_inverse t, h]
    · intro h
      rw [h, nortonUIntegerLabel_coeff]
  simp only [nortonUIntegerEmbed, Pi.single_apply, he, Int.cast_ite,
    Int.cast_one, Int.cast_zero]

private theorem eighth_sign (x y : ℝ)
    (h : (1 / 8 : ℝ) * x = (-1 / 8 : ℝ) * y) : y = -x := by
  linarith

/-- Every actual integer basis image is a signed sum of the 64 genuine compact transitions. -/
theorem monsterNortonUCompactNumerator_basis (u : Fin 4096) :
    monsterNortonUCompactNumerator (Pi.single u 1) =
      -(∑ a : XiGrayIndex, monsterNortonUCompactBasisSign (golayLabelCoefficients u) a •
        (Pi.single (nortonUIntegerLabel
          (monsterNortonUCompactBasisIndex (golayLabelCoefficients u) a)) 1 :
            NortonUIntegerVector)) := by
  funext n
  apply Int.cast_injective (α := ℝ)
  have hi : Function.Injective nortonUIntegerLabel :=
    Function.LeftInverse.injective nortonUIntegerLabel_inverse
  have hs := monsterNortonUCompactSpin_actual_embed (Pi.single u 1)
  have hn := congrFun hs (golayLabelCoefficients n)
  conv_lhs at hn =>
    rw [monsterNortonUIntegerEmbed_single, monsterNortonUCompactSpin_actual_basis]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff] at hn
  have he (a : XiGrayIndex) : n = nortonUIntegerLabel
      (monsterNortonUCompactBasisIndex (golayLabelCoefficients u) a) ↔
      golayLabelCoefficients n = monsterNortonUCompactBasisIndex (golayLabelCoefficients u) a := by
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
theorem monsterNortonUCompactNumerator_basis_fin64 (u : Fin 4096) :
    monsterNortonUCompactNumerator (Pi.single u 1) =
      -(∑ a : Fin 64,
        monsterNortonUCompactBasisSign (golayLabelCoefficients u)
          (monsterNortonGrayCoefficients a) •
        (Pi.single (nortonUIntegerLabel
          (monsterNortonUCompactBasisIndex (golayLabelCoefficients u)
            (monsterNortonGrayCoefficients a))) 1 : NortonUIntegerVector)) := by
  rw [monsterNortonUCompactNumerator_basis]
  apply congrArg (fun v : NortonUIntegerVector => -v)
  exact (Equiv.sum_comp monsterNortonGrayEquiv (fun a : XiGrayIndex =>
    monsterNortonUCompactBasisSign (golayLabelCoefficients u) a •
      (Pi.single (nortonUIntegerLabel
        (monsterNortonUCompactBasisIndex (golayLabelCoefficients u) a)) 1 :
          NortonUIntegerVector))).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
