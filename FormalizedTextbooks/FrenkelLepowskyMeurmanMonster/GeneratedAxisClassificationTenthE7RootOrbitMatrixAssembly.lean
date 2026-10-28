/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitAction

/-! The actual original matrix stabilizer decomposes over its genuine sixty-three-root orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine conjugation is a bijection of the entire actual matrix groups in both coordinates. -/
def generatedTenthE7OriginalMatrixGroupEquiv :
    generatedTenthE7StandardMatrixGroup ≃ generatedTenthE7OriginalMatrixGroup where
  toFun g := ⟨generatedTenthE7OrbitConjugation g.val, g.property⟩
  invFun h := ⟨generatedTenthE7OrbitTransport⁻¹ * h.val * generatedTenthE7OrbitTransport, by
    change generatedTenthE7OrbitConjugation
      (generatedTenthE7OrbitTransport⁻¹ * h.val * generatedTenthE7OrbitTransport) ∈
        generatedTenthE7OriginalMatrixGroup
    have he : generatedTenthE7OrbitConjugation
        (generatedTenthE7OrbitTransport⁻¹ * h.val * generatedTenthE7OrbitTransport) = h.val := by
      change generatedTenthE7OrbitTransport *
        (generatedTenthE7OrbitTransport⁻¹ * h.val * generatedTenthE7OrbitTransport) *
          generatedTenthE7OrbitTransport⁻¹ = h.val
      group
    rw [he]
    exact h.property⟩
  left_inv g := by
    apply Subtype.ext
    change generatedTenthE7OrbitTransport⁻¹ *
      (generatedTenthE7OrbitTransport * g.val * generatedTenthE7OrbitTransport⁻¹) *
        generatedTenthE7OrbitTransport = g.val
    group
  right_inv h := by
    apply Subtype.ext
    change generatedTenthE7OrbitTransport *
      (generatedTenthE7OrbitTransport⁻¹ * h.val * generatedTenthE7OrbitTransport) *
        generatedTenthE7OrbitTransport⁻¹ = h.val
    group

/-- The full actual original matrix group equals its actual root stabilizer times sixty-three. -/
theorem generatedTenth_e7_original_matrix_card_root_factor (r : generatedTenthE7RootShortSet) :
    Nat.card generatedTenthE7OriginalMatrixGroup =
      63 * Nat.card (MulAction.stabilizer generatedTenthE7StandardMatrixGroup r) := by
  rw [← Nat.card_congr generatedTenthE7OriginalMatrixGroupEquiv]
  exact generatedTenth_e7_root_short_matrix_card r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
