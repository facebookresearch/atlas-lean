/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMiddleProjector

/-! Exact actual pair-coordinate action of source Golay signs and correcting Pauli operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

private theorem code_blocks_A (a : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) x)).2.1 0 p =
      (trialityBlocksEquiv x).2.1 0 p := by
  have hm := generatedFourth_local_matrix (localFiberIncl (sourceQCode a ε)) x
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode a ε)) x)).1 =
    conwayMatrixAction 1 (griessConwayEncode x).1 at hm
  rw [map_one] at hm
  have hp := congrArg (fun M => M (griessCoordinatePair p).1 (griessCoordinatePair p).2) hm
  simpa only [griessConwayEncode, griessCoordinatePair_ne, dite_false,
    griessPairIndex_pair, LinearEquiv.coe_one, id_eq] using hp

private theorem code_blocks_C (a : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) x)).2.1 2 p =
      qSign (golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 2 p := by
  have hs := generatedFourth_local_short (localFiberIncl (sourceQCode a ε)) x
  have h0 := congrArg (fun X => X (Sum.inl (0, p))) hs
  have h1 := congrArg (fun X => X (Sum.inl (1, p))) hs
  change (griessConwayEncode (rhoLocal (inclQ (sourceQCode a ε)) x)).2.1 _ =
    localShortRepresentation (localFiberIncl (sourceQCode a ε)) _ _ at h0 h1
  rw [sourceQCode_short_pair] at h0 h1
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

set_option maxRecDepth 10000 in
-- Expand the actual source word before evaluating its dictionary pair block.
private theorem source_blocks_B (a : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv ((sourceGeneratedY a ε).val x)).2.1 1 p =
      qSign (golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).2) *
          (trialityBlocksEquiv x).2.1 1 p := by
  rw [← generatedFifth_sign_local_action, generatedFifth_sign_local_apply,
    generatedExtra_inverse_blocks]
  change (trialityCycleAction 276).symm
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) (sExtra x))).2.1 1 p = _
  rw [trialityCycleAction_inverse_apply]
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) (sExtra x))).2.1 2 p = _
  rw [code_blocks_C, generatedExtra_blocks]
  have ht : trialityCycle.symm 2 = 1 := by decide
  simp only [trialityBlockAction, LinearEquiv.prodCongr_apply, trialityCycleAction,
    LinearEquiv.piCongrLeft'_apply, ht]

set_option maxRecDepth 10000 in
-- Expand the actual source word before evaluating its dictionary pair block.
private theorem source_blocks_C (a : Fin 4096) (ε : ZMod 2) (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv ((sourceGeneratedY a ε).val x)).2.1 2 p =
      (trialityBlocksEquiv x).2.1 2 p := by
  rw [← generatedFifth_sign_local_action, generatedFifth_sign_local_apply,
    generatedExtra_inverse_blocks]
  change (trialityCycleAction 276).symm
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) (sExtra x))).2.1 2 p = _
  rw [trialityCycleAction_inverse_apply]
  change (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode a ε)) (sExtra x))).2.1 0 p = _
  rw [code_blocks_A, generatedExtra_blocks]
  have ht : trialityCycle.symm 0 = 2 := by decide
  simp only [trialityBlockAction, LinearEquiv.prodCongr_apply, trialityCycleAction,
    LinearEquiv.piCongrLeft'_apply, ht]

private theorem fifth_C_zero (p : Fin 276) :
    (trialityBlocksEquiv generatedFifthAxis).2.1 2 p = 0 := by
  have h0 := generatedFifth_final_pair_minus p
  have h1 := generatedFifth_final_pair_plus p
  simp only [griessConwayEncode, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h0 h1
  linarith

/-- Every actual source sign scales each final pair row by its genuine physical code character. -/
theorem generatedFifth_sign_source_pair (a : Fin 4096) (ε : ZMod 2) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (rhoLocal (generatedFifthSignLocal a ε) generatedFifthAxis)).2.1
      (Sum.inl (s, p)) =
      qSign (golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).2) *
          (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (s, p)) := by
  rw [generatedFifth_sign_local_action]
  simp only [griessConwayEncode, source_blocks_B, source_blocks_C, fifth_C_zero,
    add_zero, zero_sub]
  split_ifs <;> ring

/-- A Pauli operator with the given code translation has the same genuine pair character. -/
theorem generatedFifth_sign_Q_pair_phase (q : Q) (a : Fin 4096)
    (ha : spinTranslation q = golayLabelCoefficients a)
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0) (s : Fin 2) (p : Fin 276) :
    localShortPhase (localFiberIncl q) (Sum.inl (s, p)) =
      golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).1 +
        golayEncoder (golayLabelCoefficients a) (griessCoordinatePair p).2 := by
  change toAdd (spinConjugation (spinHolomorphIncl q) (griessShortQ (Sum.inl (s, p)))).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero, qBeta_spin_coordinates, qBeta_spin_coordinates,
    ha, griessPairQ_translation, griessPairQ_modulation]
  rw [spinDot_comm (golayLabelCoefficients a), griessPairSyndrome_dot]
  have ht : spinDot (Pi.single 11 1) (spinModulation q) = 0 := by
    rw [spinDot_comm, ho]
  split_ifs
  · simp [spinDot]
  · rw [ht, add_zero]

/-- Each actual corrected Golay sign fixes every original pair coordinate. -/
theorem generatedFifth_sign_corrected_pair (k : Fin 12) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.1 (Sum.inl (s, p)) =
        (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (s, p)) := by
  rw [generatedFifthSignCorrectedFiber, map_mul, generatedFifth_sign_fiber_local, map_mul]
  change (griessConwayEncode (rhoLocal
    (localFiberIntoH (localFiberIncl (generatedFifthSignCorrection k)))
      (rhoLocal (generatedFifthSignLocal (generatedFifthSignCode k) 0)
        generatedFifthAxis))).2.1 _ = _
  rw [generatedFourth_local_short, generatedFourthQ_short_coordinate]
  have ha : spinTranslation (generatedFifthSignCorrection k) =
      golayLabelCoefficients (generatedFifthSignCode k) := by
    exact generatedAxisFourthQFromSpin_translation _ _ _
  rw [generatedFifth_sign_Q_pair_phase _ _ ha (generatedFifth_sign_correction_omega k),
    generatedFifth_sign_source_pair, ← mul_assoc, qSign_sq, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
