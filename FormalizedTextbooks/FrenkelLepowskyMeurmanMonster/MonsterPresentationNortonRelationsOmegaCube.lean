/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Removing the genuine all-one code sign from Norton cubic words. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodeCube
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem inverse_triality_sign (k : Fin 3) :
    monsterSourceTriality * centralSignIntoGenerated (trialityCycle k) *
      monsterSourceTriality⁻¹ = centralSignIntoGenerated k := by
  have h : extraIntoGenerated * centralSignIntoGenerated k * extraIntoGenerated⁻¹ =
      centralSignIntoGenerated (trialityCycle k) := by
    apply Subtype.ext
    exact trialityCentralSign_conjugate k
  rw [← h, monsterSourceTriality]
  group

private theorem even_step_sign (a : Fin 2048) :
    (monsterNortonEvenStep a * centralSignIntoGenerated 2 *
      (monsterNortonEvenStep a)⁻¹ = centralSignIntoGenerated 1) ∧
    (monsterNortonEvenStep a * centralSignIntoGenerated 1 *
      (monsterNortonEvenStep a)⁻¹ = centralSignIntoGenerated 0) := by
  have h1 := inverse_triality_sign 1
  have h0 := inverse_triality_sign 0
  have hc1 := sourceGeneratedCode_commute_sign_one ⟨a.val, by omega⟩ 0
  have hc0 := localIntoGenerated_commute_central (inclQ (sourceQCode ⟨a.val, by omega⟩ 0))
  have hz : qIntoGenerated qCentralInvolution = centralSignIntoGenerated 0 := by
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign
  change sourceGeneratedCode ⟨a.val, by omega⟩ 0 * qIntoGenerated qCentralInvolution =
    qIntoGenerated qCentralInvolution * sourceGeneratedCode ⟨a.val, by omega⟩ 0 at hc0
  rw [hz] at hc0
  have ht1 : trialityCycle 1 = 2 := by decide +kernel
  have ht0 : trialityCycle 0 = 1 := by decide +kernel
  rw [ht1] at h1
  rw [ht0] at h0
  constructor
  · unfold monsterNortonEvenStep
    rw [mul_inv_rev]
    calc
      _ = sourceGeneratedCode ⟨a.val, by omega⟩ 0 *
        (monsterSourceTriality * centralSignIntoGenerated 2 * monsterSourceTriality⁻¹) *
        (sourceGeneratedCode ⟨a.val, by omega⟩ 0)⁻¹ := by group
      _ = _ := by rw [h1, hc1]; group
  · unfold monsterNortonEvenStep
    rw [mul_inv_rev]
    calc
      _ = sourceGeneratedCode ⟨a.val, by omega⟩ 0 *
        (monsterSourceTriality * centralSignIntoGenerated 1 * monsterSourceTriality⁻¹) *
        (sourceGeneratedCode ⟨a.val, by omega⟩ 0)⁻¹ := by group
      _ = _ := by rw [h0, hc0]; group

/-- Multiplying the even-code word by the actual all-one lift does not alter its cube. -/
theorem monsterNortonOmegaEvenStep_cube_eq (a : Fin 2048) :
    (qIntoGenerated sourceOmegaQ * monsterNortonEvenStep a) ^ 3 =
      monsterNortonEvenStep a ^ 3 := by
  obtain ⟨h2, h1⟩ := even_step_sign a
  have hp : centralSignIntoGenerated 2 * centralSignIntoGenerated 1 *
      centralSignIntoGenerated 0 = 1 := by
    apply Subtype.ext
    change trialityCentralSign 2 * trialityCentralSign 1 * trialityCentralSign 0 = 1
    rw [← trialityCentralSign_zero_mul_one,
      mul_assoc (trialityCentralSign 0) (trialityCentralSign 1) (trialityCentralSign 1),
      trialityCentralSign_square, mul_one, trialityCentralSign_square]
  rw [qIntoGenerated_sourceOmegaQ]
  calc
    _ = centralSignIntoGenerated 2 *
      (monsterNortonEvenStep a * centralSignIntoGenerated 2 * (monsterNortonEvenStep a)⁻¹) *
      (monsterNortonEvenStep a *
        (monsterNortonEvenStep a * centralSignIntoGenerated 2 * (monsterNortonEvenStep a)⁻¹) *
        (monsterNortonEvenStep a)⁻¹) * monsterNortonEvenStep a ^ 3 := by
          simp only [pow_succ, pow_zero]; group
    _ = _ := by rw [h2, h1, hp, one_mul]

/-- Thus the same actual cubic holds after adjoining the all-one code lift. -/
theorem monsterNortonOmegaEvenStep_cube (a : Fin 2048)
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    (qIntoGenerated sourceOmegaQ * monsterNortonEvenStep a) ^ 3 = 1 := by
  rw [monsterNortonOmegaEvenStep_cube_eq, monsterNortonEvenStep_cube a ha]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
