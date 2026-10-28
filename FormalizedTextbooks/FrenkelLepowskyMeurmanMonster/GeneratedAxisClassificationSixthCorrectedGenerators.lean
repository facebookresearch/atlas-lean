/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthXiTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignLift

/-! Five literal original local fibers and their phase-blind spatial projections.
Full-axis fixation is a separate certificate obligation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original full fiber carrying the base triple to the sixth spatial triple. -/
def generatedSixthPermutationTransportFiber : localFiberSubgroup :=
  leechRootedA2GeneratingWordFiber leechRootedA2SixthPermutationTransportWord

/-- Five unmodified original local generators of the sixth spatial flag. -/
def generatedSixthRawGenerator : Fin 5 → localFiberSubgroup :=
  let B := generatedSixthPermutationTransportFiber
  let C := leechRootedA2SixthXiTransportFiber
  ![B * representativePermutationFiber 0 * B⁻¹,
    B * representativePermutationFiber 1 * B⁻¹,
    B * representativePermutationFiber 3 * B⁻¹,
    leechRootedA2GeneratingWordFiber leechRootedA2SixthPermutationSwapWord,
    C⁻¹ * xiSpinLocalFiber * C]

/-- The actual Q corrections, with their complete preferred central signs. -/
def generatedSixthGeneratorCorrection : Fin 5 → Q :=
  ![generatedAxisFourthQFromSpin (golayLabelCoefficients 2687)
      (golayLabelCoefficients 1158) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3071)
      (golayLabelCoefficients 524) 1,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 3440)
      (golayLabelCoefficients 513) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 1276)
      (golayLabelCoefficients 1866) 0,
    generatedAxisFourthQFromSpin (golayLabelCoefficients 538)
      (golayLabelCoefficients 135) 0]

/-- The five corrected literal local fibers; their full fixation requires further certificates. -/
def generatedSixthCorrectedGenerator (k : Fin 5) : localFiberSubgroup :=
  localFiberIncl (generatedSixthGeneratorCorrection k) * generatedSixthRawGenerator k

/-- Inner Q correction does not change the genuine spatial coordinate. -/
theorem generatedSixth_corrected_generator_spatial (k : Fin 5) :
    (generatedSixthCorrectedGenerator k).val.2 = (generatedSixthRawGenerator k).val.2 := by
  change (1 : leechIsomSubgroup) * (generatedSixthRawGenerator k).val.2 = _
  exact one_mul _

/-- Each corrected fiber projects to its exact unmodified original spatial word. -/
theorem generatedSixth_corrected_generator_projection (k : Fin 5) :
    projH (localFiberIntoH (generatedSixthCorrectedGenerator k)) =
      (QuotientGroup.mk' signsSubgroup (generatedSixthRawGenerator k).val.2 : Co1) := by
  change QuotientGroup.mk' signsSubgroup (generatedSixthCorrectedGenerator k).val.2 = _
  rw [generatedSixth_corrected_generator_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
