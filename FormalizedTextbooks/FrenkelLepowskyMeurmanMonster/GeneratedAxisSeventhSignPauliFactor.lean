/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSourceSignLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignTranslation

/-! Full preferred central phases are retained in corrected original code and cocode factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem base_eq_of_spin (q r : Q)
    (ht : spinTranslation q = spinTranslation r)
    (hm : spinModulation q = spinModulation r) : q.base = r.base := by
  apply toAdd.injective
  funext i
  exact Fin.addCases
    (motive := fun i : Fin 24 => toAdd q.base i = toAdd r.base i)
    (fun j => congrFun ht j) (fun j => congrFun hm j) i

private theorem central_comm (c : ZMod 2) (q : Q) : qCentral c * q = q * qCentral c := by
  apply (q_mul_comm_iff _ _).mpr
  change qBeta 0 (toAdd q.base) = qBeta (toAdd q.base) 0
  rw [qBeta_zero_left, qBeta_zero_right]

/-- Changing the signed code parameter retains its complete original preferred central phase. -/
theorem generatedSeventh_source_code_central (d : Fin 4096) (ε : ZMod 2) :
    sourceQCode d ε = qCentral ε * sourceQCode d 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    rfl
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change ε + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) =
      ε + (0 + (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ))
    rw [zero_add]

/-- Original code lifts have even final modulation because theta pairs trivially with Omega. -/
theorem generatedSeventh_source_code_modulation_last (d : Fin 4096) (ε : ZMod 2) :
    spinModulation (sourceQCode d ε) 11 = 0 := by
  rw [sourceQCode_modulation]
  have h := sourceWordTheta_dot_omega d
  rw [sourceWordTheta_eq_polynomial] at h
  rw [spinDot_single_right] at h
  exact h

/-- Omega powers retain their actual translation and zero modulation. -/
theorem generatedSeventh_omega_power_coordinates (β : ZMod 2) :
    spinTranslation (sourceOmegaQ ^ β.val) = β • Pi.single (11 : Fin 12) 1 ∧
      spinModulation (sourceOmegaQ ^ β.val) = 0 := by
  have hβ : β = 0 ∨ β = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact h β
  rcases hβ with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, zero_smul]
    exact ⟨rfl, rfl⟩
  · simp only [ZMod.val_one, pow_one, one_smul]
    exact ⟨sourceOmegaQ_translation, sourceOmegaQ_modulation⟩

/-- A Pauli element with the corrected translation and even modulation factors into genuine
original even cocode, Omega, and signed code operators, with no central phase omitted. -/
theorem generatedSeventh_sign_pauli_factor (q : Q) (d : Fin 4096) (β : ZMod 2)
    (ht : spinTranslation q = golayLabelCoefficients d + β • Pi.single (11 : Fin 12) 1)
    (hm : spinModulation q 11 = 0) :
    ∃ m : SpinIndex, m 11 = 0 ∧ ∃ ε : ZMod 2,
      q = cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d ε := by
  let m := spinModulation q + spinModulation (sourceQCode d 0)
  have hm0 : m 11 = 0 := by
    change spinModulation q 11 + spinModulation (sourceQCode d 0) 11 = 0
    rw [hm, generatedSeventh_source_code_modulation_last, zero_add]
  let r := cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d 0
  have htr : spinTranslation r = spinTranslation q := by
    simp only [r, spinTranslation_mul, cocodeQ_translation,
      (generatedSeventh_omega_power_coordinates β).1, sourceQCode_translation, zero_add]
    exact (add_comm _ _).trans ht.symm
  have hmr : spinModulation r = spinModulation q := by
    simp only [r, spinModulation_mul, cocodeQ_modulation,
      (generatedSeventh_omega_power_coordinates β).2, add_zero]
    change (spinModulation q + spinModulation (sourceQCode d 0)) +
      spinModulation (sourceQCode d 0) = spinModulation q
    rw [add_assoc, ZModModule.add_self, add_zero]
  let ε := toAdd q.coeff + toAdd r.coeff
  have hq : q = qCentral ε * r := by
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base]
      exact base_eq_of_spin q r htr.symm hmr.symm
    · apply toAdd.injective
      rw [qCentral_mul_coeff]
      change toAdd q.coeff = (toAdd q.coeff + toAdd r.coeff) + toAdd r.coeff
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  refine ⟨m, hm0, ε, ?_⟩
  rw [hq, generatedSeventh_source_code_central]
  change qCentral ε * (cocodeQ m * sourceOmegaQ ^ β.val * sourceQCode d 0) = _
  calc
    _ = (qCentral ε * (cocodeQ m * sourceOmegaQ ^ β.val)) * sourceQCode d 0 := by
      group
    _ = ((cocodeQ m * sourceOmegaQ ^ β.val) * qCentral ε) * sourceQCode d 0 := by
      rw [central_comm]
    _ = _ := by group


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
