/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! An original phase-corrected Fifth candidate yields a genuine entire Eleventh-axis Q fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual even source cocode used in the complete original root-word calculation. -/
def generatedEleventhRootCocode : Q := cocodeQ (golayLabelCoefficients 1696)

/-- The original phase-corrected middle Pauli element, retaining its central sign. -/
def generatedEleventhMiddleRootQ : Q := qCentralInvolution * generatedEleventhRootCocode

/-- The genuine triality image retains both the central and Omega factors. -/
def generatedEleventhRootQ : Q :=
  qCentralInvolution * sourceOmegaQ * generatedEleventhRootCocode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check all original candidates using the previously proved complete original Q cache.
/-- A complete original Fifth candidate has precisely the stated genuine middle coordinates. -/
theorem generatedEleventh_middle_root_candidate_coordinates : ∃ b : ZMod 2, ∃ j : Fin 16,
    (∀ i : Fin 24, toAdd
      (generatedAxisGlobalFifthQFast 3 (generatedFifthQCandidate b j)).base i =
        toAdd generatedEleventhRootCocode.base i) ∧
      toAdd (generatedAxisGlobalFifthQFast 3 (generatedFifthQCandidate b j)).coeff = 1 := by
  decide +kernel

/-- The finite coordinate certificate identifies an entire genuine original Q element. -/
theorem generatedEleventh_middle_root_candidate : ∃ b : ZMod 2, ∃ j : Fin 16,
    generatedTenthQWordImage 3 7 (generatedFifthQCandidate b j) =
      generatedEleventhMiddleRootQ := by
  obtain ⟨b, j, hb, hc⟩ := generatedEleventh_middle_root_candidate_coordinates
  refine ⟨b, j, ?_⟩
  rw [generatedTenth_Q_word_fast 3 generatedAxisGlobalFifthQCache03_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    have hm : generatedEleventhMiddleRootQ.base = generatedEleventhRootCocode.base := by
      change (1 : Multiplicative (Fin 24 → ZMod 2)) * generatedEleventhRootCocode.base = _
      exact one_mul _
    rw [hm]
    exact funext hb
  · apply toAdd.injective
    change _ = (1 : ZMod 2)
    exact hc

/-- The actual phase-corrected Pauli element fixes every original middle-axis constituent. -/
theorem generatedEleventh_middle_root_Q_fixed :
    rhoLocal (inclQ generatedEleventhMiddleRootQ)
      (rhoLocal generatedEleventhLocal generatedFifthAxis) =
        rhoLocal generatedEleventhLocal generatedFifthAxis := by
  obtain ⟨b, j, hj⟩ := generatedEleventh_middle_root_candidate
  rw [← hj, ← generatedTenth_Q_word_image]
  have hw := generatedTenth_Q_word_fiber_local 3
  change localFiberIntoH (generatedTenthQWordFiber 3) = generatedEleventhLocal at hw
  rw [← hw, inclQ_spinConjugation, map_mul, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply]
  change rhoLocal (localFiberIntoH (generatedTenthQWordFiber 3))
    (rhoLocal (inclQ (generatedFifthQCandidate b j))
      ((rhoLocal (localFiberIntoH (generatedTenthQWordFiber 3))).symm
        (rhoLocal (localFiberIntoH (generatedTenthQWordFiber 3)) generatedFifthAxis))) = _
  rw [LinearEquiv.symm_apply_apply, generatedFifth_candidate_full_fixed]

/-- The entire actual root operator is the original forward-triality conjugate. -/
theorem generatedEleventh_root_Q_triality :
    sExtra * rhoLocal (inclQ generatedEleventhMiddleRootQ) * sExtra⁻¹ =
      rhoLocal (inclQ generatedEleventhRootQ) := by
  have he : (golayLabelCoefficients (1696 : Fin 4096)) (11 : Fin 12) = 0 := by
    decide +kernel
  have hc := (monsterNortonEvenCocode_commute_extra _ he).eq
  have hs : rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) =
      trialityCentralSign 1 := by
    rw [map_mul, map_mul]
    change localCentralGriess * rhoLocal (inclQ sourceOmegaQ) = _
    rw [localCentralGriess_eq_trialityCentralSign, sourceOmegaQ_eq_trialityCentralSign,
      ← trialityCentralSign_zero_mul_one, ← mul_assoc, trialityCentralSign_square, one_mul]
  rw [generatedEleventhMiddleRootQ, generatedEleventhRootQ, map_mul, map_mul,
    map_mul, map_mul, hs]
  change sExtra * (localCentralGriess * rhoLocal (inclQ generatedEleventhRootCocode)) *
    sExtra⁻¹ = trialityCentralSign 1 * rhoLocal (inclQ generatedEleventhRootCocode)
  have hh : sExtra * rhoLocal (inclQ generatedEleventhRootCocode) * sExtra⁻¹ =
      rhoLocal (inclQ generatedEleventhRootCocode) := by
    change sExtra * rhoLocal (inclQ (cocodeQ (golayLabelCoefficients 1696))) * sExtra⁻¹ = _
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rfl
  calc
    _ = (sExtra * localCentralGriess * sExtra⁻¹) *
        (sExtra * rhoLocal (inclQ generatedEleventhRootCocode) * sExtra⁻¹) := by group
    _ = _ := by rw [localCentralGriess_conjugate, hh]

/-- The original central phase and Omega factor fix the complete actual Eleventh axis. -/
theorem generatedEleventh_root_Q_fixed :
    rhoLocal (inclQ generatedEleventhRootQ) generatedEleventhAxis = generatedEleventhAxis := by
  rw [← generatedEleventh_root_Q_triality, generatedEleventhAxis_local_expression]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [generatedEleventh_middle_root_Q_fixed]

/-- This genuine full-axis fixer is nonidentity in the original extraspecial group. -/
theorem generatedEleventh_root_Q_ne_one : generatedEleventhRootQ ≠ 1 := by
  intro h
  have hh := congrArg (fun q : Q => spinTranslation q (11 : Fin 12)) h
  change (1 : ZMod 2) = 0 at hh
  exact one_ne_zero hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
