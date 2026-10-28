/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinSupportExact

/-! Actual Pauli fixation determines the complete signed spin state up to its zero coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original fixing Pauli element whose translation is the selected kernel coordinate. -/
def generatedSixthSpinPhaseTransport (t : SpinIndex) : Q :=
  generatedSixthSpinPauliProduct (generatedSixthSpinPauliLeftInverse *ᵥ t)

/-- A finite original binary phase formula for the complete rank-nine state. -/
def generatedSixthSpinPhaseModel (t : SpinIndex) : ℝ :=
  if generatedSixthSpinSupportMatrix *ᵥ t = 0 then
    qSign (spinPhase (generatedSixthSpinPhaseTransport t) 0)
  else 0

/-- The exact signed coefficient follows from genuine fixation at zero and the support equations. -/
theorem generatedSixth_spin_phase_model (t : SpinIndex) :
    generatedSixthSpinState t =
      generatedSixthSpinPhaseModel t * generatedSixthSpinState 0 := by
  by_cases ht : generatedSixthSpinSupportMatrix *ᵥ t = 0
  · have he : spinTranslation (generatedSixthSpinPhaseTransport t) = t := by
      rw [generatedSixthSpinPhaseTransport, generatedSixth_spin_pauli_product_translation]
      exact generatedSixth_spin_support_projection t ht
    have hf := (generatedSpinSupport_fixed_iff (generatedSixthSpinPhaseTransport t)
      generatedSixthSpinState).mp (generatedSixth_spin_pauli_product_fixed _) 0
    rw [zero_add, he] at hf
    unfold generatedSixthSpinPhaseModel
    rw [ite_eq_left ht, ← hf, ← mul_assoc, qSign_sq, one_mul]
  · have hz : generatedSixthSpinState t = 0 := by
      by_contra hz
      exact ht (generatedSixth_spin_support_equations t hz)
    rw [hz, generatedSixthSpinPhaseModel, ite_eq_right ht, zero_mul]

/-- The phase model equals zero precisely outside the actual three-equation support kernel. -/
theorem generatedSixth_spin_phase_model_zero_iff (t : SpinIndex) :
    generatedSixthSpinPhaseModel t = 0 ↔ generatedSixthSpinSupportMatrix *ᵥ t ≠ 0 := by
  unfold generatedSixthSpinPhaseModel
  split_ifs with ht
  · have hs := qSign_sq (spinPhase (generatedSixthSpinPhaseTransport t) 0)
    constructor
    · intro hz
      rw [hz, zero_mul] at hs
      exact False.elim (zero_ne_one hs)
    · intro hn
      exact False.elim (hn ht)
  · exact ⟨fun _ => ht, fun _ => rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
