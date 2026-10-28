/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Faithful recognition of the actual original C322 presentation as its explicit finite image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FaithfulnessProofs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ImageLowerBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3ParabolicFaithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original C322 presentation and actual reflection image both have order 9170703360. -/
theorem y322Orthogonal3_exact_order_faithful :
    Nat.card Y322Presentation = 9170703360 ∧
      Nat.card y322Orthogonal3Image = 9170703360 ∧
      Function.Injective y322Orthogonal3Hom :=
  y322Orthogonal3_exact_order_faithful_of_lower y322Orthogonal3Image_card_ge

/-- The eight exact source reflection matrices give an injective presentation homomorphism. -/
theorem y322Orthogonal3Hom_injective : Function.Injective y322Orthogonal3Hom :=
  y322Orthogonal3_exact_order_faithful.2.2

/-- The original presentation is isomorphic to its actual explicit characteristic-three image. -/
noncomputable def y322Orthogonal3Equiv : Y322Presentation ≃* y322Orthogonal3Image :=
  MonoidHom.ofInjective y322Orthogonal3Hom_injective

/-- The isomorphism sends every original source generator to its exact reflection matrix. -/
theorem y322Orthogonal3Equiv_generator (i : Fin 8) :
    (y322Orthogonal3Equiv (PresentedGroup.of i)).val = y322Orthogonal3Generator i := by
  exact y322Orthogonal3Hom_generator i

set_option maxRecDepth 100000 in
/-- The original E7 parabolic has exact index 3159 in the genuine original C322 group. -/
theorem y322E7Parabolic_index : y322E7Parabolic.index = 3159 := by
  have h := y322E7Parabolic.index_mul_card
  rw [y322Orthogonal3E7_exact_order_faithful.1, y322Orthogonal3_exact_order_faithful.1] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2903040)
    (h.trans (by norm_num))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
