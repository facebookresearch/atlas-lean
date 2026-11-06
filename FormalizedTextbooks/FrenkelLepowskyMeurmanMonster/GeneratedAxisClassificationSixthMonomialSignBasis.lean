/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignBasisData

/-! The ten actual sign-code columns enumerate the entire original equal-sign coefficient space. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Genuine Golay coefficients with equal bits on the actual root triple. -/
def generatedSixthSignCoefficientSpace : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
  LinearMap.ker (Matrix.toLin' generatedSixthSignConstraintMatrix)

private theorem binary_add_eq : ∀ a b : ZMod 2, a + b = 0 ↔ b = a := by decide +kernel

/-- The coefficient kernel is exactly equality of the three actual published Golay bits. -/
theorem generatedSixth_sign_coefficient_mem (t : Fin 12 → ZMod 2) :
    t ∈ generatedSixthSignCoefficientSpace ↔
      golayEncoder t 17 = golayEncoder t 16 ∧ golayEncoder t 19 = golayEncoder t 16 := by
  change generatedSixthSignConstraintMatrix *ᵥ t = 0 ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [generatedSixth_sign_constraint_encoder] at h0 h1
    change golayEncoder t 16 + golayEncoder t 17 = 0 at h0
    change golayEncoder t 16 + golayEncoder t 19 = 0 at h1
    exact ⟨(binary_add_eq _ _).mp h0, (binary_add_eq _ _).mp h1⟩
  · rintro ⟨h17, h19⟩
    funext j
    rw [generatedSixth_sign_constraint_encoder]
    fin_cases j
    · change golayEncoder t 16 + golayEncoder t 17 = 0
      rw [h17, ZModModule.add_self]
    · change golayEncoder t 16 + golayEncoder t 19 = 0
      rw [h19, ZModModule.add_self]

/-- Every ten-bit combination is a genuine equal-sign Golay coefficient vector. -/
theorem generatedSixth_sign_basis_mem (a : Fin 10 → ZMod 2) :
    generatedSixthSignBasisMatrix *ᵥ a ∈ generatedSixthSignCoefficientSpace := by
  change generatedSixthSignConstraintMatrix *ᵥ (generatedSixthSignBasisMatrix *ᵥ a) = 0
  rw [Matrix.mulVec_mulVec, generatedSixth_sign_basis_constraint, Matrix.zero_mulVec]

/-- The ten literal source-code columns reconstruct every original equal-sign coefficient. -/
theorem generatedSixth_sign_basis_reconstruct (t : generatedSixthSignCoefficientSpace) :
    generatedSixthSignBasisMatrix *ᵥ (generatedSixthSignBasisLeftInverse *ᵥ t.val) = t.val := by
  have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M *ᵥ t.val)
    generatedSixth_sign_basis_projection
  have ht : generatedSixthSignConstraintMatrix *ᵥ t.val = 0 := t.property
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ht, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

/-- The ten source-code columns enumerate the entire actual equal-sign coefficient space. -/
def generatedSixthSignCoefficientEquiv : (Fin 10 → ZMod 2) ≃ generatedSixthSignCoefficientSpace :=
  Equiv.ofBijective
    (fun a => ⟨generatedSixthSignBasisMatrix *ᵥ a, generatedSixth_sign_basis_mem a⟩)
    ⟨by
      intro a b h
      have he := congrArg (fun t : generatedSixthSignCoefficientSpace =>
        generatedSixthSignBasisLeftInverse *ᵥ t.val) h
      simpa only [Matrix.mulVec_mulVec, generatedSixth_sign_basis_left_inverse,
        Matrix.one_mulVec] using he,
    by
      intro t
      refine ⟨generatedSixthSignBasisLeftInverse *ᵥ t.val, ?_⟩
      apply Subtype.ext
      exact generatedSixth_sign_basis_reconstruct t⟩

/-- Exactly 1024 original Golay coefficient vectors have equal signs on the actual root triple. -/
theorem generatedSixthSignCoefficientSpace_card :
    Nat.card generatedSixthSignCoefficientSpace = 1024 := by
  have h := Nat.card_congr generatedSixthSignCoefficientEquiv
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at h
  norm_num at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
