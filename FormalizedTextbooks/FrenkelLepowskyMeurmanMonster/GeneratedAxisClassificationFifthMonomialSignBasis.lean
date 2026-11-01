/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! Exact original Y-basis action of the actual source Golay sign words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine preferred dictionary transport phase, including both Z normalizations. -/
noncomputable def generatedFifthSignDictionaryPhase (q : Q) (d e : Fin 2048) : ZMod 2 :=
  spinPhase q (generatedFifthSpinLow e) +
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
    (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)

/-- Actual Q action transports the entire original Z basis vector, with no dropped blocks. -/
theorem generatedFifth_sign_Q_Z_basis (q : Q) (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + spinTranslation q =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex))
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0) (i : Fin 24) :
    rhoLocal (inclQ q) (trialityXYZBasis 2 (finProdFinEquiv (d, i))) =
      qSign (generatedFifthSignDictionaryPhase q d e) •
        trialityXYZBasis 2 (finProdFinEquiv (e, i)) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode
    (localGriessRepresentation (localFiberIncl q) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  rw [show griessConwayEncode
      (qSign (generatedFifthSignDictionaryPhase q d e) •
        trialityXYZBasis 2 (finProdFinEquiv (e, i))) =
      qSign (generatedFifthSignDictionaryPhase q d e) •
        griessConwayEncode (trialityXYZBasis 2 (finProdFinEquiv (e, i))) from
    griessConwayEncodeLinear.map_smul _ _]
  rw [griessConwayEncode_Z_basis, griessConwayEncode_Z_basis]
  apply Prod.ext
  · simp only [map_zero, Prod.smul_fst, smul_zero]
  · apply Prod.ext
    · simp only [map_zero, Prod.smul_snd, Prod.smul_fst, smul_zero]
    · ext t j
      change localTensorRepresentation (localFiberIncl q) (trialityZTensor d i) t j = _
      rw [localTensorRepresentation_q]
      exact generatedFifth_sign_Z_tensor q d e h he ho i j t

/-- The source sign word has the exact checked Y-basis dictionary action. -/
theorem generatedFifth_sign_Y_basis (a : Fin 4096) (ε : ZMod 2)
    (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + golayLabelCoefficients a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (i : Fin 24) :
    rhoLocal (generatedFifthSignLocal a ε)
      (trialityXYZBasis 1 (finProdFinEquiv (d, i))) =
        qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) •
          trialityXYZBasis 1 (finProdFinEquiv (e, i)) := by
  have ho : spinDot (spinModulation (sourceQCode a ε)) (Pi.single 11 1) = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_polynomial, sourceWordTheta_dot_omega]
  have ht : generatedFifthSpinLow e + spinTranslation (sourceQCode a ε) =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex) := by
    simpa only [sourceQCode_translation] using he
  rw [generatedFifth_sign_local_apply, sExtra_XYZ_basis]
  change sExtra⁻¹ (rhoLocal (inclQ (sourceQCode a ε))
    (trialityXYZBasis 2 (finProdFinEquiv (d, i)))) = _
  rw [generatedFifth_sign_Q_Z_basis _ d e h ht ho i]
  rw [show sExtra⁻¹
      (qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) •
        trialityXYZBasis 2 (finProdFinEquiv (e, i))) =
      qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) •
        sExtra⁻¹ (trialityXYZBasis 2 (finProdFinEquiv (e, i))) from
    (sExtra⁻¹).map_smul _ _]
  have hb : sExtra⁻¹ (trialityXYZBasis 2 (finProdFinEquiv (e, i))) =
      trialityXYZBasis 1 (finProdFinEquiv (e, i)) := by
    apply sExtra.injective
    change sExtra (sExtra.symm (trialityXYZBasis 2 (finProdFinEquiv (e, i)))) = _
    rw [LinearEquiv.apply_symm_apply, sExtra_XYZ_basis]
    rfl
  exact congrArg (fun x : GriessSpace =>
    qSign (generatedFifthSignDictionaryPhase (sourceQCode a ε) d e) • x) hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
