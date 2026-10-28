/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCompactBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlanePermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! A genuine simultaneous local Xi conjugate and its exact compact spin operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal genuine Pauli correction; these coordinates retain the central sign bit. -/
def generatedSeventhXiPlaneCorrection : Q :=
  generatedAxisFourthQFromSpin (golayLabelCoefficients 1804) (golayLabelCoefficients 1613) 1

/-- The original simultaneous lift retains the genuine three-bases factor and Pauli correction. -/
def generatedSeventhXiPlaneFiber : localFiberSubgroup :=
  localFiberIncl generatedSeventhXiPlaneCorrection * generatedSeventhXiPlanePermutationFiber *
    xiSpinLocalFiber * generatedSeventhXiPlanePermutationFiber⁻¹

private def spinMap : localFiberSubgroup →* SpinHolomorph :=
  (MonoidHom.fst SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype

/-- Scalar uncertainty in the permutation lift cancels, leaving this exact source spin operator. -/
theorem generatedSeventhXiPlaneFiber_spin :
    generatedSeventhXiPlaneFiber.val.1 =
      spinHolomorphIncl generatedSeventhXiPlaneCorrection *
        (generatedSeventhXiPlaneCompactSpin * xiSpinHolomorph *
          generatedSeventhXiPlaneCompactSpin⁻¹) := by
  have h : spinMap generatedSeventhXiPlaneFiber =
      spinHolomorphIncl generatedSeventhXiPlaneCorrection *
        (generatedSeventhXiPlanePermutationFiber.val.1 * xiSpinHolomorph *
          generatedSeventhXiPlanePermutationFiber.val.1⁻¹) := by
    rw [generatedSeventhXiPlaneFiber, map_mul, map_mul, map_mul, map_inv]
    change spinHolomorphIncl generatedSeventhXiPlaneCorrection *
      generatedSeventhXiPlanePermutationFiber.val.1 * xiSpinHolomorph *
        generatedSeventhXiPlanePermutationFiber.val.1⁻¹ = _
    simp only [mul_assoc]
  change spinMap generatedSeventhXiPlaneFiber = _
  rw [h, generatedSeventhXiPlane_compact_conjugate]

private def spatialMap : localFiberSubgroup →* leechIsomSubgroup :=
  (MonoidHom.snd SpinHolomorph leechIsomSubgroup).comp localFiberSubgroup.subtype

/-- Its spatial component is the original Xi conjugated by the actual source permutation. -/
theorem generatedSeventhXiPlaneFiber_spatial :
    generatedSeventhXiPlaneFiber.val.2 =
      golayPermutationIsometry generatedSeventhXiPlanePermutation * co1XiIsometry *
        (golayPermutationIsometry generatedSeventhXiPlanePermutation)⁻¹ := by
  change spatialMap generatedSeventhXiPlaneFiber = _
  rw [generatedSeventhXiPlaneFiber, map_mul, map_mul, map_mul, map_inv]
  have hq : spatialMap (localFiberIncl generatedSeventhXiPlaneCorrection) = 1 := rfl
  have hx : spatialMap xiSpinLocalFiber = co1XiIsometry := rfl
  have hp : spatialMap generatedSeventhXiPlanePermutationFiber =
      golayPermutationIsometry generatedSeventhXiPlanePermutation :=
    generatedSeventhXiPlanePermutationFiber_spatial
  rw [hq, hx, hp, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
