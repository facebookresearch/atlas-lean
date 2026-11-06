/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full source distance-two line ratio has a phase-correct actual local conjugate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineOneThreeWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual central coefficient of the complete source-word Q transport. -/
noncomputable def monsterNortonLineOneThreeTransportPhase : ZMod 2 :=
  toAdd (monsterNortonLineOneThreeTransportImage monsterNortonLineOneThreeFourPointQ).coeff

/-- The whole actual Q image retains the defining central coefficient. -/
theorem monsterNortonLineOneThreeTransportWord_image :
    monsterNortonLineOneThreeTransportImage monsterNortonLineOneThreeFourPointQ =
      qCentral monsterNortonLineOneThreeTransportPhase * sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    funext i
    exact monsterNortonLineOneThreeTransportWord_binary i
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change monsterNortonLineOneThreeTransportPhase =
      monsterNortonLineOneThreeTransportPhase + 0
    rw [add_zero]

private theorem negative_omega_conjugate :
    extraIntoGenerated ^ 2 * qIntoGenerated (qCentral 1 * sourceOmegaQ) *
      (extraIntoGenerated ^ 2)⁻¹ = qIntoGenerated qCentralInvolution := by
  have hs : qIntoGenerated (qCentral 1 * sourceOmegaQ) = centralSignIntoGenerated 1 := by
    rw [map_mul, qIntoGenerated_sourceOmegaQ]
    apply Subtype.ext
    change localCentralGriess * trialityCentralSign 2 = trialityCentralSign 1
    rw [localCentralGriess_eq_trialityCentralSign, ← trialityCentralSign_zero_mul_one,
      ← mul_assoc, trialityCentralSign_square, one_mul]
  rw [hs]
  apply Subtype.ext
  change sExtra ^ 2 * trialityCentralSign 1 * (sExtra ^ 2)⁻¹ = localCentralGriess
  calc
    _ = sExtra * (sExtra * trialityCentralSign 1 * sExtra⁻¹) * sExtra⁻¹ := by
      simp only [pow_two]
      group
    _ = localCentralGriess := by
      rw [trialityCentralSign_conjugate, show trialityCycle 1 = 2 by decide,
        trialityCentralSign_conjugate, show trialityCycle 2 = 0 by decide]
      exact localCentralGriess_eq_trialityCentralSign.symm

private theorem corrected_omega_conjugate (c : ZMod 2) :
    extraIntoGenerated ^ (if c = 0 then 1 else 2) * qIntoGenerated (qCentral c * sourceOmegaQ) *
      (extraIntoGenerated ^ (if c = 0 then 1 else 2))⁻¹ = qIntoGenerated qCentralInvolution := by
  have hc : c = 0 ∨ c = 1 := by
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
    exact h c
  rcases hc with rfl | rfl
  · simp only [ite_true, pow_one, show qCentral (0 : ZMod 2) = 1 from rfl, one_mul]
    exact monsterNortonSourceY_omega_conjugate
  · simp only [show (1 : ZMod 2) ≠ 0 by decide, ite_false]
    exact negative_omega_conjugate

/-- The explicit source word includes the actual central-phase correction determined above. -/
noncomputable def monsterNortonLineOneThreeLocalWord : G :=
  (extraIntoGenerated ^ (if monsterNortonLineOneThreeTransportPhase = 0 then 1 else 2) *
    monsterNortonLineOneThreeTransportWord) *
    (y555NortonLine monsterSourceTriality 1 * (y555NortonLine monsterSourceTriality 3)⁻¹) *
      (extraIntoGenerated ^ (if monsterNortonLineOneThreeTransportPhase = 0 then 1 else 2) *
        monsterNortonLineOneThreeTransportWord)⁻¹

/-- This fully specified, phase-correct conjugate of the distance-two ratio belongs to actual H. -/
theorem monsterNortonLineOneThreeLocalWord_mem_local :
    monsterNortonLineOneThreeLocalWord ∈ localIntoGenerated.range := by
  have h := (monsterNortonLineOneThree_commutes_fourPoint.conj
    monsterNortonLineOneThreeTransportWord).conj
      (extraIntoGenerated ^ (if monsterNortonLineOneThreeTransportPhase = 0 then 1 else 2))
  rw [monsterNortonLineOneThreeTransportWord_conjugation,
    monsterNortonLineOneThreeTransportWord_image, corrected_omega_conjugate] at h
  have hw : extraIntoGenerated ^ (if monsterNortonLineOneThreeTransportPhase = 0 then 1 else 2) *
      (monsterNortonLineOneThreeTransportWord *
        (y555NortonLine monsterSourceTriality 1 *
          (y555NortonLine monsterSourceTriality 3)⁻¹) * monsterNortonLineOneThreeTransportWord⁻¹) *
      (extraIntoGenerated ^ (if monsterNortonLineOneThreeTransportPhase = 0 then 1 else 2))⁻¹ =
        monsterNortonLineOneThreeLocalWord := by
    rw [monsterNortonLineOneThreeLocalWord]
    group
  rw [hw] at h
  rw [← generatedCentralizer_eq_local_range]
  exact Subgroup.mem_centralizer_singleton_iff.mpr h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
