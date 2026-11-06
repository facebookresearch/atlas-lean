/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortSupport

/-! Original inverse Fourier and cached preferred-Q phases for the actual fifth sign lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original DH matrix squares to its transpose, without any spectral assumptions. -/
theorem generatedFifth_triality_matrix_square :
    trialityRealMatrix * trialityRealMatrix = trialityRealMatrix.transpose := by
  have hm : trialityIntegerMatrix.map (Int.castRingHom ℝ) *
      trialityIntegerMatrix.map (Int.castRingHom ℝ) =
      (8 : ℝ) • (trialityIntegerMatrix.transpose.map (Int.castRingHom ℝ)) := by
    change (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix *
      (Int.castRingHom ℝ).mapMatrix trialityIntegerMatrix = _
    rw [← map_mul, trialityIntegerMatrix_square]
    ext i j
    change ((8 • trialityIntegerMatrix.transpose) i j : ℝ) =
      8 * (trialityIntegerMatrix.transpose i j : ℝ)
    simp
  simp only [trialityRealMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm]
  ext i j
  simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
  ring

/-- The inverse original octad triality is the exact transposed DH matrix. -/
theorem generatedFifth_inverse_octad_action (X : Fin 64 → ℝ) :
    trialityOctadAction.symm X = trialityRealMatrix.transpose.mulVec X := by
  have h : trialityOctadAction.symm X = trialityOctadAction (trialityOctadAction X) := by
    apply trialityOctadAction.injective
    rw [LinearEquiv.apply_symm_apply, trialityOctadAction_triple]
  rw [h, trialityOctadAction_matrix, trialityOctadAction_matrix,
    Matrix.mulVec_mulVec, generatedFifth_triality_matrix_square]

/-- Original inverse triality has the transposed DH formula on every actual octad coordinate. -/
theorem generatedFifth_inverse_triality_octad (x : GriessSpace) (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra⁻¹ x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ f : Fin 64, trialityRealMatrix f e *
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inl (o, f))) := by
  have h : (griessConwayEncode (sExtra⁻¹ x)).2.1 (Sum.inr (Sum.inl (o, e))) =
      trialityOctadAction.symm (fun f => (griessConwayEncode x).2.1
        (Sum.inr (Sum.inl (o, f)))) e := by
    simp only [griessConwayEncode, generatedExtra_inverse_blocks,
      trialityBlockAction, LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
    rfl
  rw [h, generatedFifth_inverse_octad_action]
  rfl

/-- Executable actual short conjugation phase evaluated through the genuine physical cache. -/
def generatedFifthSignCachedShortPhase (q : Q) (r : generatedFifthXiShortCachedLabel) : ZMod 2 :=
  qBeta (toAdd q.base) (toAdd (generatedFifthXiShortCachedQ r).base) +
    qBeta (toAdd (generatedFifthXiShortCachedQ r).base) (toAdd q.base)

/-- The finite cached character is the implemented preferred-short coordinate phase. -/
theorem generatedFifth_sign_cached_phase_actual (q : Q) (r : generatedFifthXiShortCachedLabel) :
    localShortPhase (localFiberIncl q)
      (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r)) =
        generatedFifthSignCachedShortPhase q r := by
  rw [localAxisQPhase_eq_short_phase]
  change qBeta (toAdd q.base)
      (toAdd (griessShortQ (generatedFifthXiEvenShortIndex
        (generatedFifthXiShortCachedEven r))).base) +
    qBeta (toAdd (griessShortQ (generatedFifthXiEvenShortIndex
      (generatedFifthXiShortCachedEven r))).base) (toAdd q.base) = _
  rw [← generatedFifthXiEvenShortQ_actual, ← generatedFifthXiShortCachedQ_actual]
  rfl

/-- Triality of the final fifth-axis octad row is the transposed original source column. -/
theorem generatedFifth_sign_input_octad (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode (sExtra generatedFifthAxis)).2.1
      (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        trialityRealMatrix (generatedFifthEvenRootSign j) e *
          qSign (generatedFifthEvenCoefficientPhase j) := by
  rw [generatedFourthQShortBasis_triality_octad]
  simp_rw [generatedFifth_final_octad_coordinate]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have h := congrArg (fun M : Matrix (Fin 64) (Fin 64) ℝ =>
    M e (generatedFifthEvenRootSign j)) generatedFifth_triality_matrix_square
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
    congrArg (fun a : ℝ => a * qSign (generatedFifthEvenCoefficientPhase j)) h

/-- The actual source sign word acts by inverse Fourier, its full Q character, and triality. -/
theorem generatedFifth_sign_octad_action (a : Fin 4096) (ε : ZMod 2) (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode (rhoLocal (generatedFifthSignLocal a ε) generatedFifthAxis)).2.1
      (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        ∑ f : Fin 64, trialityRealMatrix f e *
          qSign (generatedFifthSignCachedShortPhase (sourceQCode a ε) (Sum.inr (j, f))) *
          trialityRealMatrix (generatedFifthEvenRootSign j) f *
          qSign (generatedFifthEvenCoefficientPhase j) := by
  rw [generatedFifth_sign_local_apply, generatedFifth_inverse_triality_octad]
  apply Finset.sum_congr rfl
  intro f _
  rw [show inclQ (sourceQCode a ε) =
    localFiberIntoH (localFiberIncl (sourceQCode a ε)) from rfl,
    generatedFourth_local_short, generatedFourthQ_short_coordinate]
  have hp := generatedFifth_sign_cached_phase_actual (sourceQCode a ε) (Sum.inr (j, f))
  change localShortPhase (localFiberIncl (sourceQCode a ε))
    (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, f))) = _ at hp
  rw [hp, generatedFifth_sign_input_octad]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
