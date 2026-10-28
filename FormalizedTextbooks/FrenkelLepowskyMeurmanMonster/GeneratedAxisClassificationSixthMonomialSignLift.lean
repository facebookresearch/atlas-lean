/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSignPauliProjectionCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardQLocal

/-! Actual full-axis lifts of the ten equal-sign spatial generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Literal source labels of the genuine Ω-adjusted fixing translations. -/
def generatedSixthSignPauliLabel : Fin 10 → Fin 4096 :=
  ![2049, 2050, 2052, 8, 96, 176, 304, 528, 3104, 0]

/-- Each literal label is exactly the actual chosen Pauli translation. -/
theorem generatedSixth_sign_pauli_label_certificate (j : Fin 10) :
    generatedSixthSignPauliTranslation j =
      golayLabelCoefficients (generatedSixthSignPauliLabel j) := by
  fin_cases j <;> decide +kernel

/-- The genuine local lift is the exact forward triality conjugate of a full middle fixer. -/
def generatedSixthMonomialSignLift (j : Fin 10) : H :=
  generatedForwardQLocal (generatedSixthSignPauliChoice j) (generatedSixth_sign_pauli_even j)

/-- Every selected sign lift fixes every actual coordinate of the sixth axis. -/
theorem generatedSixth_monomial_sign_lift_fixed (j : Fin 10) :
    rhoLocal (generatedSixthMonomialSignLift j) generatedSixthAxis = generatedSixthAxis := by
  rw [generatedSixthMonomialSignLift, generatedForwardQLocal_action,
    generatedSixthAxis_local_expression]
  simp only [LinearEquiv.mul_apply]
  change sExtra (rhoLocal (inclQ (generatedSixthSignPauliChoice j))
    (sExtra.symm (sExtra generatedSixthMiddleAxis))) = sExtra generatedSixthMiddleAxis
  rw [LinearEquiv.symm_apply_apply, generatedSixth_sign_pauli_full_fixed]

/-- The actual lifted projection is precisely the intended original source sign class. -/
theorem generatedSixth_monomial_sign_lift_projection (j : Fin 10) :
    projH (generatedSixthMonomialSignLift j) =
      (QuotientGroup.mk
        (golaySignIsometry
          (sourceGeneratedSignCode (generatedSixthMonomialSignCode j))) : Co1) := by
  rw [generatedSixthMonomialSignLift, generatedForwardQLocal_projection _ _
    (generatedSixthSignPauliLabel j)
    ((generatedSixth_sign_pauli_translation j).trans
      (generatedSixth_sign_pauli_label_certificate j))]
  have hc : sourceGeneratedSignCode (generatedSixthSignPauliLabel j) =
      generatedSixthSignPauliCode j := by
    apply Subtype.ext
    change golayEncoder (golayLabelCoefficients (generatedSixthSignPauliLabel j)) =
      golayEncoder (generatedSixthSignPauliTranslation j)
    rw [generatedSixth_sign_pauli_label_certificate]
  rw [hc]
  exact generatedSixth_sign_pauli_code_class j

/-- All ten genuine source signs belong to the actual projected full-axis stabilizer. -/
theorem generatedSixth_monomial_sign_projected_mem (j : Fin 10) :
    (QuotientGroup.mk
      (golaySignIsometry (sourceGeneratedSignCode (generatedSixthMonomialSignCode j))) : Co1) ∈
        generatedSixthProjectedAxisStabilizer := by
  rw [← generatedSixth_monomial_sign_lift_projection]
  exact ⟨⟨generatedSixthMonomialSignLift j, generatedSixth_monomial_sign_lift_fixed j⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
