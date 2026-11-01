/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The concrete, phase-correct source-word conjugate of the first line pair lies in actual H. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsFourPointWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem negative_omega_sign :
    qIntoGenerated (qCentral 1 * sourceOmegaQ) = centralSignIntoGenerated 1 := by
  rw [map_mul, qIntoGenerated_sourceOmegaQ]
  apply Subtype.ext
  change localCentralGriess * trialityCentralSign 2 = trialityCentralSign 1
  rw [localCentralGriess_eq_trialityCentralSign, ← trialityCentralSign_zero_mul_one,
    ← mul_assoc, trialityCentralSign_square, one_mul]

private theorem negative_omega_conjugate :
    extraIntoGenerated ^ 2 * qIntoGenerated (qCentral 1 * sourceOmegaQ) *
      (extraIntoGenerated ^ 2)⁻¹ = qIntoGenerated qCentralInvolution := by
  rw [negative_omega_sign]
  apply Subtype.ext
  change sExtra ^ 2 * trialityCentralSign 1 * (sExtra ^ 2)⁻¹ = localCentralGriess
  calc
    _ = sExtra * (sExtra * trialityCentralSign 1 * sExtra⁻¹) * sExtra⁻¹ := by
      simp only [pow_two]
      group
    _ = localCentralGriess := by
      rw [trialityCentralSign_conjugate, show trialityCycle 1 = 2 by decide +kernel,
        trialityCentralSign_conjugate, show trialityCycle 2 = 0 by decide +kernel]
      exact localCentralGriess_eq_trialityCentralSign.symm

/-- A fully specified source word conjugating the first line difference into actual H. -/
noncomputable def monsterNortonLineZeroOneLocalWord : ↥G :=
  (extraIntoGenerated ^ 2 * monsterNortonFourPointWord) *
    (y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹) *
      (extraIntoGenerated ^ 2 * monsterNortonFourPointWord)⁻¹

/-- The explicit word lies in actual H, with the inverse-permutation central phase retained. -/
theorem monsterNortonLineZeroOneLocalWord_mem_local :
    monsterNortonLineZeroOneLocalWord ∈ localIntoGenerated.range := by
  have h := (monsterNortonLineZeroOne_commutes_fourPoint.conj
    monsterNortonFourPointWord).conj (extraIntoGenerated ^ 2)
  rw [monsterNortonFourPointWord_conjugation, monsterNortonFourPointWord_image,
    negative_omega_conjugate] at h
  have hw : extraIntoGenerated ^ 2 *
      (monsterNortonFourPointWord *
        (y555NortonLine monsterSourceTriality 0 *
          (y555NortonLine monsterSourceTriality 1)⁻¹) * monsterNortonFourPointWord⁻¹) *
        (extraIntoGenerated ^ 2)⁻¹ = monsterNortonLineZeroOneLocalWord := by
    rw [monsterNortonLineZeroOneLocalWord]
    group
  rw [hw] at h
  rw [← generatedCentralizer_eq_local_range]
  exact Subgroup.mem_centralizer_singleton_iff.mpr h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
