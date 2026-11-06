/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source code and cocode covariance for the exact zero-phase Singer permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialSourceAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual theta modulation is transported by the genuine zero-phase permutation. -/
theorem monsterNortonSinger_theta_transport (a : SpinIndex) :
    monsterMonomialPullback (monsterNortonSingerCode 0).symm
      (sourceCodeThetaPolynomial a) = sourceCodeThetaPolynomial (monsterNortonSingerCode 0 a) := by
  ext j
  have h := monsterNortonSingerThetaDifference_zero 0 a
    ((monsterNortonSingerCode 0).symm (Pi.single j 1))
  unfold monsterNortonSingerThetaDifference at h
  rw [LinearEquiv.apply_symm_apply, spinDot_single_right] at h
  change spinDot (sourceCodeThetaPolynomial a)
    ((monsterNortonSingerCode 0).symm (Pi.single j 1)) = _
  exact ((add_eq_zero_iff_eq_neg.mp h).trans (CharTwo.neg_eq _)).symm

/-- The genuine permutation preserves the source quarter-weight central correction. -/
theorem monsterNortonSinger_quarter_weight (d e : Fin 4096)
    (he : golayLabelCoefficients e = monsterNortonSingerCode 0 (golayLabelCoefficients d)) :
    ((golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) : ZMod 2) =
      ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) := by
  have h := monsterNortonSingerThetaDifference_zero 0
    (golayLabelCoefficients d) (golayLabelCoefficients d)
  unfold monsterNortonSingerThetaDifference at h
  rw [← he, sourceCodeThetaPolynomial_self_dot, sourceCodeThetaPolynomial_self_dot] at h
  exact (add_eq_zero_iff_eq_neg.mp h).trans (CharTwo.neg_eq _)

/-- The actual spin image sends every source signed code to its permuted code with exact phase. -/
theorem monsterNortonSingerImage_code (d e : Fin 4096) (ε : ZMod 2)
    (he : golayLabelCoefficients e = monsterNortonSingerCode 0 (golayLabelCoefficients d)) :
    monsterNortonSingerImage (sourceQCode d ε) = sourceQCode e ε := by
  apply monsterMonomialQ_ext
  · change spinTranslation (monsterMonomialPermutationImage _ _) = _
    rw [monsterMonomialPermutationImage_translation, sourceQCode_translation,
      sourceQCode_translation, he]
  · change spinModulation (monsterMonomialPermutationImage _ _) = _
    rw [monsterMonomialPermutationImage_modulation, sourceQCode_modulation,
      monsterNortonSinger_theta_transport, sourceQCode_modulation, he]
  · change toAdd (sourceQCode d ε).coeff = toAdd (sourceQCode e ε).coeff
    rw [monsterSourceQCode_coefficient, monsterSourceQCode_coefficient,
      monsterNortonSinger_quarter_weight d e he]

/-- The genuine zero-phase Singer operator transports every source cocode by pullback. -/
theorem monsterNortonSingerImage_cocode (δ : SpinIndex) :
    monsterNortonSingerImage (sourceQCocode δ) =
      sourceQCocode (monsterMonomialPullback (monsterNortonSingerCode 0).symm δ) := by
  apply monsterMonomialQ_ext
  · change spinTranslation (monsterMonomialPermutationImage _ _) = _
    rw [monsterMonomialPermutationImage_translation, sourceQCocode_translation,
      sourceQCocode_translation, map_zero]
  · change spinModulation (monsterMonomialPermutationImage _ _) = _
    rw [monsterMonomialPermutationImage_modulation, sourceQCocode_modulation,
      sourceQCocode_modulation]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
