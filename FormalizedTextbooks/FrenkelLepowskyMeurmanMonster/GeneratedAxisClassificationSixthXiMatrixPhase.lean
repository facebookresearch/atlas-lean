/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiCoordinatePhase

/-! Direct matrix multiplication retains the original C character pullback and quadratic shear. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Character pullback by original inverse C is the exact transposed C matrix action. -/
theorem generatedSixth_C_pullback_matrix (m : SpinIndex) :
    monsterMonomialPullback generatedSixthCTranslation.symm m =
      (representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1)).transpose *ᵥ m := by
  ext j
  change spinDot m
    (representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) *ᵥ Pi.single j 1) = _
  rw [Matrix.mulVec_single_one]
  change (∑ i, m i * representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) i j) =
    ∑ i, representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1) i j * m i
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The original quadratic derivative equals its exact symmetric matrix acting on translation. -/
theorem generatedSixth_gradient_matrix (M : Matrix (Fin 12) (Fin 12) (ZMod 2))
    (u : SpinIndex) : monsterMonomialGradient (fun i j => M i j) u =
      (M.transpose + M) *ᵥ u := by
  ext j
  change (∑ i, u i * (M i j + M j i)) = ∑ i, (M i j + M j i) * u i
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Original C modulation computed by the two exact matrices, with the full shear retained. -/
def generatedSixthCMatrixModulation (u m : SpinIndex) : SpinIndex :=
  (representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1)).transpose *ᵥ m +
    ((representativeMatrix (generatedSixthPermutationProfilePhaseRows 1)).transpose +
      representativeMatrix (generatedSixthPermutationProfilePhaseRows 1)) *ᵥ
        generatedSixthCTranslation u

/-- The direct matrix evaluation is the complete original modulation formula. -/
theorem generatedSixth_C_matrix_modulation (u m : SpinIndex) :
    generatedSixthCMatrixModulation u m = generatedSixthCCoordinateModulation u m := by
  rw [generatedSixthCCoordinateModulation, generatedSixth_C_pullback_matrix,
    generatedSixth_gradient_matrix]
  rfl

/-- Preferred Xi phase with direct original matrix modulation and both genuine grey quadratics. -/
def generatedSixthXiMatrixPhase (u m v w : SpinIndex) : ZMod 2 :=
  let gamma := xiGrayDual (fun i =>
    spinDot (xiGrayCocodeBasis i) (generatedSixthCTranslation u))
  let grey := xiGrayDual (fun i =>
    spinDot (generatedSixthCMatrixModulation u m) (xiGrayCodeBasis i))
  monsterMonomialQuadratic
      (fun i j => representativeMatrix (generatedSixthPermutationProfilePhaseRows 1) i j)
      (generatedSixthCTranslation u) +
    xiGrayQuadratic gamma + xiGrayQuadratic (gamma + grey) +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1)) v +
    spinDot (golayLabelCoefficients 135) v + spinDot (golayLabelCoefficients 538) w

/-- Direct matrix phases equal the entire original preferred-Q phase on every true pair record. -/
theorem generatedSixth_xi_pair_matrix_phase (j : Fin 552) :
    generatedSixthXiPairExecutablePhase j =
      generatedSixthXiMatrixPhase
        (golayLabelCoefficients (generatedSixthXiPairSourceQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairSourceQ j).2)
        (golayLabelCoefficients (generatedSixthXiPairOutputQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairOutputQ j).2) := by
  rw [generatedSixth_xi_pair_coordinate_phase]
  simp only [generatedSixthXiCoordinatePhase, generatedSixthXiMatrixPhase,
    generatedSixth_C_matrix_modulation]


/-- True preferred Q coordinates give the complete original matrix-phase formula on any short. -/
theorem generatedSixth_xi_short_matrix_phase (r s : GriessShortIndex)
    (u m v w : SpinIndex)
    (hi : griessShortQ r = generatedAxisFourthQFromSpin u m 0)
    (ho : griessShortQ s = generatedAxisFourthQFromSpin v w 0) :
    generatedSixthXiShortDirectPhase r s = generatedSixthXiMatrixPhase u m v w := by
  have hc : generatedSixthGeneratorCorrection 4 = generatedAxisFourthQFromSpin
      (golayLabelCoefficients 538) (golayLabelCoefficients 135) 0 := rfl
  unfold generatedSixthXiShortDirectPhase
  rw [generatedFourthQShortBasis_character, hc,
    generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation,
    hi, ho]
  simp only [generatedSixthXiMatrixPhase, xiGrayGammaProjection, xiGrayGProjection,
    generatedSixth_C_coordinate_translation, generatedSixth_C_coordinate_modulation,
    generatedSixth_C_coordinate_coefficient, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation, generatedAxisFourthQFromSpin_coeff, zero_add,
    generatedSixth_C_matrix_modulation]
  ring

/-- Physical label transport and full preferred Q data determine the true corrected operator. -/
theorem generatedSixth_xi_short_matrix_operator (r s : GriessShortIndex)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s)
    (u m v w : SpinIndex)
    (hi : griessShortQ r = generatedAxisFourthQFromSpin u m 0)
    (ho : griessShortQ s = generatedAxisFourthQFromSpin v w 0)
    (X : GriessShortIndex → ℝ) :
    localShortOperator (generatedSixthCorrectedGenerator 4) X s =
      qSign (generatedSixthXiMatrixPhase u m v w) * X r := by
  rw [generatedSixth_xi_short_direct_operator r s hs X,
    generatedSixth_xi_short_matrix_phase r s u m v w hi ho]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
