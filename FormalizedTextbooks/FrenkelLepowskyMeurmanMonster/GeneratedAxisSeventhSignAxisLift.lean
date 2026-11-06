/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignPauliFactor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhMiddleSpinFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhProjection

/-! Genuine full-axis lifts of every actual triangle-compatible original Golay sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual central signs transport to the complete source Omega powers in the middle frame. -/
theorem generatedSeventh_central_omega_transport (β : ZMod 2) :
    qIntoGenerated (qCentral β) * extraIntoGenerated =
      extraIntoGenerated * qIntoGenerated (sourceOmegaQ ^ β.val) := by
  have hβ : β = 0 ∨ β = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact h β
  rcases hβ with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, map_one, mul_one]
    have hz : qCentral 0 = 1 := rfl
    rw [hz, map_one, one_mul]
  · simp only [ZMod.val_one, pow_one]
    have h := generatedSeventh_inverse_central
    change extraIntoGenerated⁻¹ * qIntoGenerated (qCentral 1) * extraIntoGenerated =
      qIntoGenerated sourceOmegaQ at h
    calc
      _ = extraIntoGenerated *
          (extraIntoGenerated⁻¹ * qIntoGenerated (qCentral 1) * extraIntoGenerated) := by
        group
      _ = _ := by rw [h]

/-- The genuine corrected local sign combines even cocode, central sign, and opposite code word. -/
def generatedSeventhCorrectedSignLocal (m : SpinIndex) (β : ZMod 2)
    (d : Fin 4096) (ε : ZMod 2) : H :=
  inclQ (cocodeQ m) * inclQ (qCentral β) * generatedSeventhSourceSignLocal d ε

/-- Its complete group word is the actual triality conjugate of all three Pauli factors. -/
theorem generatedSeventh_corrected_sign_generated (m : SpinIndex) (hm : m 11 = 0)
    (β : ZMod 2) (d : Fin 4096) (ε : ZMod 2) :
    localIntoGenerated (generatedSeventhCorrectedSignLocal m β d ε) =
      extraIntoGenerated *
        qIntoGenerated (cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d ε) *
          extraIntoGenerated⁻¹ := by
  have hc : qIntoGenerated (cocodeQ m) * extraIntoGenerated =
      extraIntoGenerated * qIntoGenerated (cocodeQ m) :=
    (monsterNortonEvenCocode_generated_commute_extra m hm).eq
  simp only [generatedSeventhCorrectedSignLocal, map_mul,
    generatedSeventh_source_sign_local_generated, generatedSeventhSourceZ]
  change qIntoGenerated (cocodeQ m) * qIntoGenerated (qCentral β) *
    (extraIntoGenerated * qIntoGenerated (sourceQCode d ε) * extraIntoGenerated⁻¹) = _
  calc
    _ = qIntoGenerated (cocodeQ m) *
        (qIntoGenerated (qCentral β) * extraIntoGenerated) *
          qIntoGenerated (sourceQCode d ε) * extraIntoGenerated⁻¹ := by group
    _ = qIntoGenerated (cocodeQ m) *
        (extraIntoGenerated * qIntoGenerated (sourceOmegaQ ^ β.val)) *
          qIntoGenerated (sourceQCode d ε) * extraIntoGenerated⁻¹ := by
      rw [generatedSeventh_central_omega_transport]
    _ = (qIntoGenerated (cocodeQ m) * extraIntoGenerated) *
        qIntoGenerated (sourceOmegaQ ^ β.val) *
          qIntoGenerated (sourceQCode d ε) * extraIntoGenerated⁻¹ := by group
    _ = _ := by rw [hc]; group

/-- The entire original Griess action agrees with the actual corrected Pauli conjugate. -/
theorem generatedSeventh_corrected_sign_apply (m : SpinIndex) (hm : m 11 = 0)
    (β : ZMod 2) (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    rhoLocal (generatedSeventhCorrectedSignLocal m β d ε) x =
      sExtra (rhoLocal (inclQ (cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d ε))
        (sExtra⁻¹ x)) := by
  have h := congrArg Subtype.val
    (generatedSeventh_corrected_sign_generated m hm β d ε)
  change rhoLocal (generatedSeventhCorrectedSignLocal m β d ε) =
    (extraIntoGenerated *
      qIntoGenerated (cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d ε) *
        extraIntoGenerated⁻¹).val at h
  rw [h]
  rfl

/-- Correction leaves the actual Conway projection equal to the original physical Golay sign. -/
theorem generatedSeventh_corrected_sign_projection (m : SpinIndex) (β : ZMod 2)
    (d : Fin 4096) (ε : ZMod 2) :
    projH (generatedSeventhCorrectedSignLocal m β d ε) =
      (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  simp only [generatedSeventhCorrectedSignLocal, map_mul, projH_inclQ,
    one_mul, generatedSeventh_source_sign_local_projection]

/-- Every actual triangle-compatible original Golay sign has a genuine full-coordinate axis lift. -/
theorem generatedSeventh_sign_axis_lift (d : Fin 4096)
    (hd : golayLabelCoefficients d ∈ generatedSeventhSignParameterSpace) :
    ∃ h : H, rhoLocal h generatedSeventhAxis = generatedSeventhAxis ∧
      projH h =
        (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) := by
  obtain ⟨q, ht, hm, hq⟩ := generatedSeventh_sign_fixing_pauli (golayLabelCoefficients d) hd
  obtain ⟨m, hm0, ε, he⟩ := generatedSeventh_sign_pauli_factor q d
    (generatedSeventhSignOmegaCorrection (golayLabelCoefficients d)) ht hm
  refine ⟨generatedSeventhCorrectedSignLocal m
    (generatedSeventhSignOmegaCorrection (golayLabelCoefficients d)) d ε, ?_,
    generatedSeventh_corrected_sign_projection _ _ _ _⟩
  rw [generatedSeventh_corrected_sign_apply m hm0,
    generatedSeventhAxis_local_expression, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply, ← he,
    generatedSeventh_middle_spin_fixed_axis q hq]

/-- The actual projected full-axis stabilizer contains every admissible original Golay sign. -/
theorem generatedSeventh_sign_mem_projected (d : Fin 4096)
    (hd : golayLabelCoefficients d ∈ generatedSeventhSignParameterSpace) :
    (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) ∈
      generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨h, hh, hp⟩ := generatedSeventh_sign_axis_lift d hd
  exact ⟨⟨h, hh⟩, hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
