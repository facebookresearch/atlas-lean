/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Transporting the independent full finite-form order bound through its exact diagonal basis. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact basis conjugation maps independent Cartan isometries to diagonal isometries. -/
def y322Orthogonal3GramDiagonalHom :
    y322GramIsometryGroup y322Orthogonal3Gram →* y322Orthogonal3DiagonalGroup where
  toFun g := ⟨y322Orthogonal3DiagonalBasis⁻¹ * g.val * y322Orthogonal3DiagonalBasis, by
    have h := y322GramIsometryGroup_conjugate y322Orthogonal3Gram
      y322Orthogonal3DiagonalBasis g.val g.property
    change _ ∈ y322GramIsometryGroup y322Orthogonal3DiagonalGram
    have hb : y322Orthogonal3DiagonalBasis.val.transpose * y322Orthogonal3Gram *
        y322Orthogonal3DiagonalBasis.val = y322Orthogonal3DiagonalGram :=
      y322Orthogonal3DiagonalBasis_gram
    rw [hb] at h
    exact h⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

/-- Exact conjugation by an actual basis is injective on independent Cartan isometries. -/
theorem y322Orthogonal3GramDiagonalHom_injective :
    Function.Injective y322Orthogonal3GramDiagonalHom := by
  intro g h heq
  apply Subtype.ext
  have hval := congrArg Subtype.val heq
  change y322Orthogonal3DiagonalBasis⁻¹ * g.val * y322Orthogonal3DiagonalBasis =
    y322Orthogonal3DiagonalBasis⁻¹ * h.val * y322Orthogonal3DiagonalBasis at hval
  exact mul_left_cancel (mul_right_cancel hval)

/-- The independently defined full Cartan isometry group has order at most 18341406720. -/
theorem y322Orthogonal3GramGroup_card_le :
    Nat.card (y322GramIsometryGroup y322Orthogonal3Gram) ≤ 18341406720 :=
  (Nat.card_le_card_of_injective _ y322Orthogonal3GramDiagonalHom_injective).trans
    y322Orthogonal3DiagonalGroup_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
