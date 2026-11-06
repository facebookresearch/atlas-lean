/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The checked actual local presentation splits into its commutator factor and central sign. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3CentralProductProofs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Faithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual corrected longest-word involution is central in the original local presentation. -/
theorem y322CentralInvolution_commute (x : Y322Presentation) :
    y322CentralInvolution * x = x * y322CentralInvolution :=
  y322CentralInvolution_commute_of_injective y322Orthogonal3Hom_injective x

/-- The actual source group is its genuine determinant kernel times the central sign group. -/
noncomputable def y322SignProductEquiv :
    y322Orthogonal3Sign.ker × (ZMod 3)ˣ ≃* Y322Presentation :=
  y322SignProductEquivOfInjective y322Orthogonal3Hom_injective

/-- The actual source commutator factor has order 4585351680. -/
theorem y322Presentation_commutator_card :
    Nat.card (commutator Y322Presentation) = 4585351680 := by
  have hu : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h := Nat.card_congr y322SignProductEquiv.toEquiv
  rw [Nat.card_prod, hu, y322Orthogonal3_exact_order_faithful.1] at h
  rw [← y322Orthogonal3Sign_ker]
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
