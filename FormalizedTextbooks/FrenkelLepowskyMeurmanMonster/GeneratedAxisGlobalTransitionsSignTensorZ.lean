/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! Actual original Golay sign words on the second physical tensor dictionary sector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual Q element acts diagonally on the entire original X basis vector. -/
theorem generatedAxisGlobalQ_X_basis (q : Q) (d : Fin 2048) (i : Fin 24) :
    rhoLocal (inclQ q) (trialityXYZBasis 0 (finProdFinEquiv (d, i))) =
      qSign (localShortPhase (localFiberIncl q) (Sum.inr (Sum.inr (d, i)))) •
        trialityXYZBasis 0 (finProdFinEquiv (d, i)) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  rw [show griessConwayEncode
      (qSign (localShortPhase (localFiberIncl q) (Sum.inr (Sum.inr (d, i)))) •
        trialityXYZBasis 0 (finProdFinEquiv (d, i))) =
      qSign (localShortPhase (localFiberIncl q) (Sum.inr (Sum.inr (d, i)))) •
        griessConwayEncode (trialityXYZBasis 0 (finProdFinEquiv (d, i))) from
    griessConwayEncodeLinear.map_smul _ _]
  rw [griessConwayEncode_X_basis]
  apply Prod.ext
  · simp only [map_zero, Prod.smul_fst, smul_zero]
  · apply Prod.ext
    · funext r
      change localShortOperator (localFiberIncl q)
        (Pi.single (Sum.inr (Sum.inr (d, i))) 1) r =
        qSign (localShortPhase (localFiberIncl q) (Sum.inr (Sum.inr (d, i)))) *
          (Pi.single (Sum.inr (Sum.inr (d, i))) 1 : GriessShortIndex → ℝ) r
      rw [generatedFourthQ_short_coordinate]
      by_cases hr : r = Sum.inr (Sum.inr (d, i))
      · subst r
        rfl
      · simp [hr]
    · simp only [map_zero, Prod.smul_snd, smul_zero]

/-- Every original source sign word has its actual diagonal Z-sector phase. -/
theorem generatedAxisGlobalSign_Z_basis (a : Fin 4096) (ε : ZMod 2)
    (d : Fin 2048) (i : Fin 24) :
    rhoLocal (generatedFifthSignLocal a ε) (trialityXYZBasis 2 (finProdFinEquiv (d, i))) =
      qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) • trialityXYZBasis 2 (finProdFinEquiv (d, i)) := by
  rw [generatedFifth_sign_local_apply, sExtra_XYZ_basis]
  change sExtra⁻¹ (rhoLocal (inclQ (sourceQCode a ε))
    (trialityXYZBasis 0 (finProdFinEquiv (d, i)))) = _
  rw [generatedAxisGlobalQ_X_basis]
  rw [show sExtra⁻¹
      (qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) • trialityXYZBasis 0 (finProdFinEquiv (d, i))) =
      qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) •
        sExtra⁻¹ (trialityXYZBasis 0 (finProdFinEquiv (d, i))) from
    (sExtra⁻¹).map_smul _ _]
  have hb : sExtra⁻¹ (trialityXYZBasis 0 (finProdFinEquiv (d, i))) =
      trialityXYZBasis 2 (finProdFinEquiv (d, i)) := by
    apply sExtra.injective
    change sExtra (sExtra.symm (trialityXYZBasis 0 (finProdFinEquiv (d, i)))) = _
    rw [LinearEquiv.apply_symm_apply, sExtra_XYZ_basis]
    rfl
  exact congrArg (fun x : GriessSpace =>
    qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
      (Sum.inr (Sum.inr (d, i)))) • x) hb

/-- The whole actual local tensor representation has the same exact Z-sector phase. -/
theorem generatedAxisGlobalSign_tensor_Z (a : Fin 4096) (ε : ZMod 2)
    (d : Fin 2048) (i : Fin 24) :
    localTensorRepresentation (generatedFifthSignFiber a ε) (trialityZTensor d i) =
      qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) • trialityZTensor d i := by
  have hh := generatedAxisGlobalSign_Z_basis a ε d i
  rw [← generatedFifth_sign_fiber_local] at hh
  have ht := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.2) hh
  rw [generatedFourth_local_tensor, griessConwayEncode_Z_basis] at ht
  rw [show griessConwayEncode
      (qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) • trialityXYZBasis 2 (finProdFinEquiv (d, i))) =
      qSign (localShortPhase (localFiberIncl (sourceQCode a ε))
        (Sum.inr (Sum.inr (d, i)))) •
        griessConwayEncode (trialityXYZBasis 2 (finProdFinEquiv (d, i))) from
    griessConwayEncodeLinear.map_smul _ _]
    at ht
  rw [griessConwayEncode_Z_basis] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
