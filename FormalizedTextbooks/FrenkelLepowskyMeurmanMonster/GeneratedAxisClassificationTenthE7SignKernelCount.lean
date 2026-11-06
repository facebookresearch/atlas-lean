/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignFixing

/-! Cardinality of the complete actual unsigned-line Golay-sign kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complement-octad word is nonzero in the original Golay code. -/
theorem generatedTenth_e7_complement_code_ne_zero : generatedTenthE7ComplementCode ≠ 0 := by
  intro h
  have hh := congrArg (fun c : golayCode => c.val 4) h
  rw [generatedTenth_e7_complement_coordinates] at hh
  norm_num [generatedTenthE7OctadSupport] at hh

/-- The complete actual unsigned-line sign kernel, stated using genuine lattice actions. -/
def generatedTenthE7UnsignedSignKernel :=
  {c : golayCode // (∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0) ∧
    (leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      generatedTenthE7NormTwelveLine ∨
    leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      -generatedTenthE7NormTwelveLine)}

/-- The two words give a bijection with the entire actual unsigned-line sign kernel. -/
def generatedTenthE7UnsignedSignKernelEquiv : Bool ≃ generatedTenthE7UnsignedSignKernel where
  toFun b := if b then ⟨generatedTenthE7ComplementCode, by
      constructor
      · intro i hi
        rw [generatedTenth_e7_complement_coordinates, ite_eq_left hi]
      · exact Or.inr generatedTenth_e7_complement_negates_norm_twelve⟩
    else ⟨0, by
      constructor
      · intro i _; rfl
      · exact Or.inl ((generatedTenth_e7_sign_positive_iff 0 (by intro i _; rfl)).mpr rfl)⟩
  invFun c := if c.val = 0 then false else true
  left_inv b := by
    cases b <;> simp [generatedTenth_e7_complement_code_ne_zero]
  right_inv c := by
    apply Subtype.ext
    rcases (generatedTenth_e7_sign_unsigned_iff c.val c.property.1).mp c.property.2 with h | h
    · simp [h]
    · simp [h, generatedTenth_e7_complement_code_ne_zero]

/-- Exactly two original Golay signs fix E8 positively and the norm-twelve line unsigned. -/
theorem generatedTenth_e7_unsigned_sign_kernel_card :
    Nat.card generatedTenthE7UnsignedSignKernel = 2 := by
  rw [← Nat.card_congr generatedTenthE7UnsignedSignKernelEquiv]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
