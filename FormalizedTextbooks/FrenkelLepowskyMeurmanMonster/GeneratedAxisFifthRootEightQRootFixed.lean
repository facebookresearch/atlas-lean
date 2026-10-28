/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightParityNonzero
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! An original phase-corrected Fifth candidate yields a genuine entire root-eight-axis Q fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual even source cocode used in the complete original root-word calculation. -/
def generatedFifthRootEightRootCocode : Q := cocodeQ (golayLabelCoefficients 1504)

/-- The original phase-corrected middle Pauli element, retaining its central sign. -/
def generatedFifthRootEightMiddleRootQ : Q :=
  qCentralInvolution * sourceOmegaQ * generatedFifthRootEightRootCocode

/-- The genuine triality image retains its actual Omega and cocode factors. -/
def generatedFifthRootEightRootQ : Q :=
  sourceOmegaQ * generatedFifthRootEightRootCocode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check all original candidates using the previously proved complete original Q cache.
/-- A complete original Fifth candidate has precisely the stated genuine middle coordinates. -/
theorem generatedFifthRootEight_middle_root_candidate_coordinates : ∃ b : ZMod 2, ∃ j : Fin 16,
    (∀ i : Fin 24, toAdd
      (generatedAxisGlobalFifthQFast 8 (generatedFifthQCandidate b j)).base i =
        toAdd generatedFifthRootEightMiddleRootQ.base i) ∧
      toAdd (generatedAxisGlobalFifthQFast 8 (generatedFifthQCandidate b j)).coeff = 1 := by
  decide +kernel

/-- The finite coordinate certificate identifies an entire genuine original Q element. -/
theorem generatedFifthRootEight_middle_root_candidate : ∃ b : ZMod 2, ∃ j : Fin 16,
    generatedTenthQWordImage 8 7 (generatedFifthQCandidate b j) =
      generatedFifthRootEightMiddleRootQ := by
  obtain ⟨b, j, hb, hc⟩ := generatedFifthRootEight_middle_root_candidate_coordinates
  refine ⟨b, j, ?_⟩
  rw [generatedTenth_Q_word_fast 8 generatedAxisGlobalFifthQCache08_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact funext hb
  · apply toAdd.injective
    have hm : toAdd generatedFifthRootEightMiddleRootQ.coeff = 1 := by
      decide +kernel
    rw [hm]
    exact hc

/-- The actual phase-corrected Pauli element fixes every original middle-axis constituent. -/
theorem generatedFifthRootEight_middle_root_Q_fixed :
    rhoLocal (inclQ generatedFifthRootEightMiddleRootQ)
      (rhoLocal generatedFifthRootEightLocal generatedFifthAxis) =
        rhoLocal generatedFifthRootEightLocal generatedFifthAxis := by
  obtain ⟨b, j, hj⟩ := generatedFifthRootEight_middle_root_candidate
  rw [← hj, ← generatedTenth_Q_word_image]
  have hw := generatedTenth_Q_word_fiber_local 8
  change localFiberIntoH (generatedTenthQWordFiber 8) = generatedFifthRootEightLocal at hw
  rw [← hw, inclQ_spinConjugation, map_mul, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply]
  change rhoLocal (localFiberIntoH (generatedTenthQWordFiber 8))
    (rhoLocal (inclQ (generatedFifthQCandidate b j))
      ((rhoLocal (localFiberIntoH (generatedTenthQWordFiber 8))).symm
        (rhoLocal (localFiberIntoH (generatedTenthQWordFiber 8)) generatedFifthAxis))) = _
  rw [LinearEquiv.symm_apply_apply, generatedFifth_candidate_full_fixed]

/-- The entire actual root operator is the original forward-triality conjugate. -/
theorem generatedFifthRootEight_root_Q_triality :
    sExtra * rhoLocal (inclQ generatedFifthRootEightMiddleRootQ) * sExtra⁻¹ =
      rhoLocal (inclQ generatedFifthRootEightRootQ) := by
  have he : (golayLabelCoefficients (1504 : Fin 4096)) (11 : Fin 12) = 0 := by
    decide +kernel
  have hc := (monsterNortonEvenCocode_commute_extra _ he).eq
  have hs : rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) =
      trialityCentralSign 1 := by
    rw [map_mul, map_mul]
    change localCentralGriess * rhoLocal (inclQ sourceOmegaQ) = _
    rw [localCentralGriess_eq_trialityCentralSign, sourceOmegaQ_eq_trialityCentralSign,
      ← trialityCentralSign_zero_mul_one, ← mul_assoc, trialityCentralSign_square, one_mul]
  have hh : sExtra * rhoLocal (inclQ generatedFifthRootEightRootCocode) * sExtra⁻¹ =
      rhoLocal (inclQ generatedFifthRootEightRootCocode) := by
    change sExtra * rhoLocal (inclQ (cocodeQ (golayLabelCoefficients 1504))) * sExtra⁻¹ = _
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rfl
  have hm : rhoLocal (inclQ generatedFifthRootEightMiddleRootQ) =
      trialityCentralSign 1 * rhoLocal (inclQ generatedFifthRootEightRootCocode) := by
    rw [generatedFifthRootEightMiddleRootQ, map_mul, map_mul, hs]
  have ho : rhoLocal (inclQ generatedFifthRootEightRootQ) =
      trialityCentralSign 2 * rhoLocal (inclQ generatedFifthRootEightRootCocode) := by
    rw [generatedFifthRootEightRootQ, map_mul, map_mul, sourceOmegaQ_eq_trialityCentralSign]
  rw [hm, ho]
  calc
    _ = (sExtra * trialityCentralSign 1 * sExtra⁻¹) *
        (sExtra * rhoLocal (inclQ generatedFifthRootEightRootCocode) * sExtra⁻¹) := by group
    _ = _ := by
      rw [trialityCentralSign_conjugate, show trialityCycle 1 = 2 by decide, hh]

/-- The original Omega and cocode factors fix the complete actual root-eight axis. -/
theorem generatedFifthRootEight_root_Q_fixed :
    rhoLocal (inclQ generatedFifthRootEightRootQ) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis := by
  rw [← generatedFifthRootEight_root_Q_triality, generatedFifthRootEightAxis_local_expression]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [generatedFifthRootEight_middle_root_Q_fixed]

/-- This genuine full-axis fixer is nonidentity in the original extraspecial group. -/
theorem generatedFifthRootEight_root_Q_ne_one : generatedFifthRootEightRootQ ≠ 1 := by
  intro h
  have hh := congrArg (fun q : Q => spinTranslation q (11 : Fin 12)) h
  change (1 : ZMod 2) = 0 at hh
  exact one_ne_zero hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
