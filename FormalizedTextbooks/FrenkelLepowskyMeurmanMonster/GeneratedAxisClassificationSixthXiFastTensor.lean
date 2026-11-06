/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorIntegerAction

/-! Exact bit-parity spin profiles and the checked original Gaussian evaluate the full Xi tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete signed integer action of literal source rows, using exact bit parity. -/
def generatedSixthSpinMaskInteger (coordinate phase : Fin 12 → Fin 4096)
    (v : NortonUIntegerVector) (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (if (generatedSixthMonomialMaskQuadratic
      (fun i => (phase i).val) n.val).testBit 0 then 1 else 0) *
    v (generatedSixthMonomialMaskLabel coordinate n.val)

/-- Bit parity gives the complete original signed matrix action on every integer vector. -/
theorem generatedSixth_spin_mask_integer (coordinate phase : Fin 12 → Fin 4096)
    (v : NortonUIntegerVector) :
    generatedSixthSpinMaskInteger coordinate phase v =
      generatedSixthSpinIntegerModel (representativeSpinRowsModel coordinate phase) v := by
  funext n
  have hl : generatedSixthMonomialMaskLabel coordinate n.val =
      nortonUIntegerLabel (representativeMatrix coordinate *ᵥ golayLabelCoefficients n) := by
    apply golayLabelCoefficients_injective
    rw [generatedSixth_monomial_mask_label, nortonUIntegerLabel_inverse]
    rfl
  have hq := generatedSixth_monomial_mask_quadratic (fun i => (phase i).val) n.val
  change (if (generatedSixthMonomialMaskQuadratic
      (fun i => (phase i).val) n.val).testBit 0 then (1 : ZMod 2) else 0) =
    monsterMonomialQuadratic (representativeMatrix phase) (golayLabelCoefficients n) at hq
  rw [generatedSixthSpinMaskInteger, hl, hq]
  rfl

/-- Exact inverse-C, all 64 original Gaussian terms, and C, retaining both quadratic signs. -/
def generatedSixthXiFastSpinInteger (v : NortonUIntegerVector) : NortonUIntegerVector :=
  generatedSixthSpinMaskInteger (generatedSixthPermutationProfileInverseCoordinateRows 1)
    (generatedSixthPermutationProfileInversePhaseRows 1)
    (generatedSixthIntegerXiCached
      (generatedSixthSpinMaskInteger (generatedSixthPermutationProfileCoordinateRows 1)
        (generatedSixthPermutationProfilePhaseRows 1) v))

/-- The fast evaluator is exactly the entire original conjugated-Xi spin numerator. -/
theorem generatedSixth_xi_fast_spin_integer (v : NortonUIntegerVector) :
    generatedSixthXiFastSpinInteger v = generatedSixthXiSpinInteger v := by
  rw [generatedSixthXiFastSpinInteger, generatedSixth_spin_mask_integer,
    generatedSixth_spin_mask_integer, ← generatedSixth_integer_xi_cached]
  rfl

/-- The complete cleared raw tensor retains every physical row and original Gaussian term. -/
def generatedSixthXiFastRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, sixthFrameOrbitSpatialNumerator 14 i j *
    generatedSixthXiFastSpinInteger (fun m => generatedSixthTensorExecutable m j) n

/-- Exact preferred Q phase and translation act on the full cleared Xi tensor. -/
def generatedSixthXiFastTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      1 else 0) *
    generatedSixthXiFastRawTensor (generatedSixthSpinLabelXor n 538) i

/-- The executable Xi tensor retains the entire actual preferred correction and original action. -/
theorem generatedSixth_xi_fast_tensor_numerator (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiFastTensor n i = generatedSixthXiTensorInteger n i := by
  have hq : generatedSixthGeneratorCorrection 4 =
      generatedAxisFourthQFromSpin
        (golayLabelCoefficients 538) (golayLabelCoefficients 135) 0 :=
    rfl
  have hl : generatedSixthSpinLabelXor n 538 =
      nortonUIntegerLabel (golayLabelCoefficients n +
        spinTranslation (generatedSixthGeneratorCorrection 4)) := by
    apply golayLabelCoefficients_injective
    rw [generatedSixth_spin_label_xor, nortonUIntegerLabel_inverse,
      hq, generatedAxisFourthQFromSpin_translation]
  have hp : (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      (1 : ZMod 2) else 0) =
        spinPhase (generatedSixthGeneratorCorrection 4) (golayLabelCoefficients n) := by
    rw [monsterCo1GeometryBinaryMaskDot_decode, hq]
    simp only [spinPhase, generatedAxisFourthQFromSpin_coeff,
      generatedAxisFourthQFromSpin_modulation, zero_add]
    rfl
  simp only [generatedSixthXiFastTensor, hl, hp, generatedSixthXiFastRawTensor,
    generatedSixth_xi_fast_spin_integer, generatedSixthXiTensorInteger,
    generatedSixthXiRawTensorInteger]

/-- Exact bit parity and certified Gaussians evaluate the whole genuine corrected tensor. -/
theorem generatedSixth_xi_fast_tensor (n : Fin 4096) (i : Fin 24) :
    localTensorRepresentation (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i =
        (generatedSixthXiFastTensor n i : ℝ) / (512 * Real.sqrt 2) := by
  rw [generatedSixth_xi_fast_tensor_numerator]
  exact generatedSixth_xi_corrected_tensor_integer n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
