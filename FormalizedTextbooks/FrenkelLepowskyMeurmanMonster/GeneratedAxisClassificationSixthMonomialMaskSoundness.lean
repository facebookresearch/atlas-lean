/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorAction

/-! Direct bit-parity arithmetic is exactly the full original corrected monomial tensor action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Decoded XOR is precisely translation by the actual preferred Q correction. -/
theorem generatedSixth_monomial_mask_translated (k : Fin 4) (n : Fin 4096) :
    monsterCo1GeometryBinaryMaskDecode
      (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val) =
        golayLabelCoefficients n +
          spinTranslation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) := by
  change monsterCo1GeometryBinaryMaskDecode
    (Nat.xor n.val (generatedSixthMonomialMaskTranslation k).val) = _
  rw [monsterCo1GeometryBinaryMaskDecode_xor, generatedSixth_monomial_mask_correction,
    generatedAxisFourthQFromSpin_translation]
  rfl

/-- The direct affine source label is the complete original matrix pullback after Q translation. -/
theorem generatedSixth_monomial_fast_pull (k : Fin 4) (n : Fin 4096) :
    generatedSixthMonomialFastPull k n =
      nortonUIntegerLabel ((generatedSixthMonomialSpinModel k).coordinate *ᵥ
        (golayLabelCoefficients n +
          spinTranslation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)))) := by
  apply golayLabelCoefficients_injective
  rw [generatedSixthMonomialFastPull, generatedSixth_monomial_mask_label,
    nortonUIntegerLabel_inverse, generatedSixth_monomial_mask_translated,
    ← generatedSixth_monomial_mask_coordinate]

/-- Direct bit parity retains the entire actual Q central phase and original quadratic phase. -/
theorem generatedSixth_monomial_fast_phase (k : Fin 4) (n : Fin 4096) :
    generatedSixthMonomialFastPhase k n =
      spinPhase (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) (golayLabelCoefficients n) +
        monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
          (golayLabelCoefficients n +
            spinTranslation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k))) := by
  have hc : toAdd (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)).coeff =
      generatedSixthMonomialMaskCentral k := by
    rw [generatedSixth_monomial_mask_correction, generatedAxisFourthQFromSpin_coeff]
  have hm : spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) =
      golayLabelCoefficients (generatedSixthMonomialMaskModulation k) := by
    rw [generatedSixth_monomial_mask_correction, generatedAxisFourthQFromSpin_modulation]
  have hd : (if (monsterCo1GeometryBinaryMaskDot 12
      (generatedSixthMonomialMaskModulation k).val n.val).testBit 0 then (1 : ZMod 2) else 0) =
        spinDot (spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)))
          (golayLabelCoefficients n) := by
    rw [monsterCo1GeometryBinaryMaskDot_decode, hm]
    rfl
  have hq := generatedSixth_monomial_mask_quadratic
    (fun i => (generatedSixthMonomialMaskPhaseRows k i).val)
    (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val)
  change (if (generatedSixthMonomialMaskQuadratic
      (fun i => (generatedSixthMonomialMaskPhaseRows k i).val)
      (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val)).testBit 0 then
        (1 : ZMod 2) else 0) =
      monsterMonomialQuadratic (representativeMatrix (generatedSixthMonomialMaskPhaseRows k))
        (monsterCo1GeometryBinaryMaskDecode
          (n.val ^^^ (generatedSixthMonomialMaskTranslation k).val)) at hq
  rw [generatedSixth_monomial_mask_translated, ← generatedSixth_monomial_mask_phase] at hq
  rw [generatedSixthMonomialFastPhase, hd, hq, ← hc]
  rfl

/-- Direct integer arithmetic retains the true affine label, central sign and physical row. -/
def generatedSixthMonomialFastTensor (k : Fin 4) (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (generatedSixthMonomialFastPhase k n) *
    generatedSixthTensorExecutable (generatedSixthMonomialFastPull k n)
      (generatedSixthMonomialPhysicalInput k i)

/-- The bit-parity expression is exactly the full original corrected integer tensor formula. -/
theorem generatedSixth_monomial_fast_tensor_numerator (k : Fin 4)
    (n : Fin 4096) (i : Fin 24) :
    generatedSixthMonomialFastTensor k n i = generatedSixthMonomialTensorNumerator k n i := by
  rw [generatedSixthMonomialFastTensor, generatedSixth_monomial_fast_pull,
    generatedSixth_monomial_fast_phase, generatedSixth_tensor_executable_eq]
  rfl

/-- Exact bit-parity arithmetic evaluates the complete original corrected tensor coordinate. -/
theorem generatedSixth_monomial_fast_tensor (k : Fin 4) (n : Fin 4096) (i : Fin 24) :
    localTensorRepresentation (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i =
        (generatedSixthMonomialFastTensor k n i : ℝ) / (32 * Real.sqrt 2) := by
  rw [generatedSixth_monomial_fast_tensor_numerator]
  exact generatedSixth_monomial_corrected_tensor k n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
