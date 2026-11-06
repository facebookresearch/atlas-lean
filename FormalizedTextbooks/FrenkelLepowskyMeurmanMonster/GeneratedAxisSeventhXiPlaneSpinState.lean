/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinSupportExact

/-! The genuine fixing Pauli products determine the middle spin state up to its scalar sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The normalized state uses actual fixing-product phases and the proved support equations. -/
def generatedSeventhXiPlaneNormalizedSpin (t : SpinIndex) : ℝ :=
  if generatedSeventhSpinSupportMatrix *ᵥ t = 0 then
    qSign (spinPhase
      (generatedSeventhSpinPauliProduct (generatedSeventhSpinPauliLeftInverse *ᵥ t)) 0) / 16
  else 0

/-- Every genuine middle coefficient is its normalized phase times the zero coefficient. -/
theorem generatedSeventhXiPlane_spin_normalized (t : SpinIndex) :
    generatedSeventhSpinState t =
      (16 * generatedSeventhSpinState 0) * generatedSeventhXiPlaneNormalizedSpin t := by
  by_cases ht : generatedSeventhSpinSupportMatrix *ᵥ t = 0
  · let a := generatedSeventhSpinPauliLeftInverse *ᵥ t
    have he : spinTranslation (generatedSeventhSpinPauliProduct a) = t := by
      rw [generatedSeventh_spin_pauli_product_translation]
      exact generatedSeventh_spin_support_projection t ht
    have h := (generatedSpinSupport_fixed_iff _ _).mp
      (generatedSeventh_spin_pauli_product_fixed a) 0
    rw [zero_add, he] at h
    have hs := qSign_sq (spinPhase (generatedSeventhSpinPauliProduct a) 0)
    simp only [generatedSeventhXiPlaneNormalizedSpin, ht, ite_true]
    dsimp only [a] at h hs
    have hh := congrArg (fun z : ℝ =>
      qSign (spinPhase (generatedSeventhSpinPauliProduct
        (generatedSeventhSpinPauliLeftInverse *ᵥ t)) 0) * z) h
    rw [← mul_assoc, hs, one_mul] at hh
    rw [hh]
    ring
  · have hz : generatedSeventhSpinState t = 0 := by
      by_contra hn
      exact ht (generatedSeventh_spin_support_equations t hn)
    simp only [generatedSeventhXiPlaneNormalizedSpin, ht, ite_false, mul_zero, hz]

/-- The remaining scalar is exactly a sign; no unchecked basis coefficient selects it. -/
theorem generatedSeventhXiPlane_spin_normalized_sign :
    generatedSeventhSpinState = generatedSeventhXiPlaneNormalizedSpin ∨
      generatedSeventhSpinState = -generatedSeventhXiPlaneNormalizedSpin := by
  have h := generatedSeventh_spin_kernel_square_exact 0 (by simp)
  have hs : (16 * generatedSeventhSpinState 0) = 1 ∨
      (16 * generatedSeventhSpinState 0) = -1 := by
    have hh : (16 * generatedSeventhSpinState 0) ^ 2 = 1 := by nlinarith
    have hf : (16 * generatedSeventhSpinState 0 - 1) *
        (16 * generatedSeventhSpinState 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hs with hs | hs
  · left
    funext t
    rw [generatedSeventhXiPlane_spin_normalized, hs, one_mul]
  · right
    funext t
    rw [generatedSeventhXiPlane_spin_normalized, hs, neg_one_mul]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
