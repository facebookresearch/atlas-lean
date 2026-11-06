/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCodeOmegaFactor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityKleinFour

/-! The genuine triality conjugate of the all-one code and every high source factor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generated_sign_zero :
    centralSignIntoGenerated 0 = qIntoGenerated qCentralInvolution := by
  apply Subtype.ext
  exact localCentralGriess_eq_trialityCentralSign.symm

private theorem generated_sign_zero_two :
    centralSignIntoGenerated 0 * centralSignIntoGenerated 2 =
      centralSignIntoGenerated 1 := by
  apply Subtype.ext
  change trialityCentralSign 0 * trialityCentralSign 2 = trialityCentralSign 1
  rw [← trialityCentralSign_zero_mul_one, ← mul_assoc,
    trialityCentralSign_square, one_mul]

/-- The literal all-one source sign is the genuine product of the two Q involutions. -/
theorem generatedAxisGlobalSourceY_omega :
    sourceGeneratedY 2048 0 = qIntoGenerated (qCentralInvolution * sourceOmegaQ) := by
  have h : extraIntoGenerated * centralSignIntoGenerated 1 * extraIntoGenerated⁻¹ =
      centralSignIntoGenerated 2 := by
    apply Subtype.ext
    have hc := trialityCentralSign_conjugate 1
    rw [show trialityCycle 1 = 2 from by decide +kernel] at hc
    exact hc
  rw [sourceGeneratedY, sourceGeneratedCode, generatedAxisGlobalSourceCode_omega,
    qIntoGenerated_sourceOmegaQ, ← h]
  have hi : extraIntoGenerated⁻¹ *
      (extraIntoGenerated * centralSignIntoGenerated 1 * extraIntoGenerated⁻¹) *
        extraIntoGenerated = centralSignIntoGenerated 1 := by group
  rw [hi, ← generated_sign_zero_two, generated_sign_zero,
    ← qIntoGenerated_sourceOmegaQ, map_mul]

/-- Every high source sign is the actual all-one sign followed by its low source sign. -/
theorem generatedAxisGlobalSourceY_high_factor (a : Fin 2048) (ε : ZMod 2) :
    sourceGeneratedY (generatedAxisGlobalCodeHighLabel a) ε =
      qIntoGenerated (qCentralInvolution * sourceOmegaQ) *
        sourceGeneratedY (generatedAxisGlobalCodeLowLabel a) ε := by
  rw [← generatedAxisGlobalSourceY_omega]
  simp only [sourceGeneratedY, sourceGeneratedCode]
  rw [generatedAxisGlobalCodeHigh_factor, map_mul,
    generatedAxisGlobalSourceCode_omega]
  group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
