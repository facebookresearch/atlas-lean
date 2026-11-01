/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! The original C/Gaussian central phase is evaluated directly in genuine spin coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original C modulation is the pulled-back character plus its genuine quadratic shear. -/
def generatedSixthCCoordinateModulation (u m : SpinIndex) : SpinIndex :=
  monsterMonomialPullback generatedSixthCTranslation.symm m +
    monsterMonomialGradient
      (fun i j => representativeMatrix (generatedSixthPermutationProfilePhaseRows 1) i j)
      (generatedSixthCTranslation u)

/-- The full C image has its actual translation without rebuilding its extension coordinates. -/
theorem generatedSixth_C_coordinate_translation (q : Q) :
    spinTranslation (generatedSixthCImage q) =
      generatedSixthCTranslation (spinTranslation q) := by
  rw [generatedSixthCImage, monsterMonomialDiagonalImage_translation,
    monsterMonomialPermutationImage_translation]

/-- The full C image has its genuine pulled-back and sheared modulation coordinates. -/
theorem generatedSixth_C_coordinate_modulation (q : Q) :
    spinModulation (generatedSixthCImage q) =
      generatedSixthCCoordinateModulation (spinTranslation q) (spinModulation q) := by
  rw [generatedSixthCImage, monsterMonomialDiagonalImage_modulation,
    monsterMonomialPermutationImage_modulation, monsterMonomialPermutationImage_translation]
  rfl

/-- The C central coefficient retains the original input bit and complete source quadratic. -/
theorem generatedSixth_C_coordinate_coefficient (q : Q) :
    toAdd (generatedSixthCImage q).coeff = toAdd q.coeff +
      monsterMonomialQuadratic
        (fun i j => representativeMatrix (generatedSixthPermutationProfilePhaseRows 1) i j)
        (generatedSixthCTranslation (spinTranslation q)) := by
  change toAdd q.coeff + monsterMonomialQuadratic _
    (spinTranslation (monsterMonomialPermutationImage generatedSixthCTranslation q)) = _
  rw [monsterMonomialPermutationImage_translation]

/-- Complete original preferred phase on actual source and target Schrödinger coordinates. -/
def generatedSixthXiCoordinatePhase (u m v w : SpinIndex) : ZMod 2 :=
  let gamma := xiGrayDual (fun i =>
    spinDot (xiGrayCocodeBasis i) (generatedSixthCTranslation u))
  let grey := xiGrayDual (fun i =>
    spinDot (generatedSixthCCoordinateModulation u m) (xiGrayCodeBasis i))
  monsterMonomialQuadratic
      (fun i j => representativeMatrix (generatedSixthPermutationProfilePhaseRows 1) i j)
      (generatedSixthCTranslation u) +
    xiGrayQuadratic gamma + xiGrayQuadratic (gamma + grey) +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1)) v +
    spinDot (golayLabelCoefficients 135) v + spinDot (golayLabelCoefficients 538) w

/-- Direct spin-coordinate evaluation equals the entire original preferred-Q phase. -/
theorem generatedSixth_xi_pair_coordinate_phase (j : Fin 552) :
    generatedSixthXiPairExecutablePhase j =
      generatedSixthXiCoordinatePhase
        (golayLabelCoefficients (generatedSixthXiPairSourceQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairSourceQ j).2)
        (golayLabelCoefficients (generatedSixthXiPairOutputQ j).1)
        (golayLabelCoefficients (generatedSixthXiPairOutputQ j).2) := by
  simp only [generatedSixthXiPairExecutablePhase, generatedSixthXiCoordinatePhase,
    xiGrayGammaProjection, xiGrayGProjection,
    generatedSixth_C_coordinate_translation, generatedSixth_C_coordinate_modulation,
    generatedSixth_C_coordinate_coefficient, generatedSixthXiPackedQ,
    generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation,
    generatedAxisFourthQFromSpin_coeff, zero_add]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
