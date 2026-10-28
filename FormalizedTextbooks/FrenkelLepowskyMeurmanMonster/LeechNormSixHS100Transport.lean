/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Action

/-! Genuine Conway transports between actual norm-four/norm-six flags and their point sets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every genuine norm-four/norm-six flag of pairing sixteen reaches the complete canonical flag. -/
theorem leechNormSixHS100Flag_transport (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16) :
    ∃ g : leechIsomSubgroup, leechIntegralAction g x = leechNormSixHS100Root ∧
      leechIntegralAction g y = leechNormSixHS100Companion := by
  obtain ⟨a, ha⟩ := leechNormSixActualPair_root_transport x hx
  obtain ⟨b, hb⟩ := leechNormSixActualPair_root_transport
    leechNormSixHS100Root leechNormSixHS100Root_square
  let e : leechIsomSubgroup := b⁻¹ * a
  have he : leechIntegralAction e x = leechNormSixHS100Root := by
    change leechIntegralAction (b⁻¹ * a) x = _
    rw [map_mul, LinearEquiv.mul_apply, ha, ← hb,
      ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hys : leechSquareSum (leechIntegralAction e y).val = 48 := by
    rw [leechIntegralAction_squareSum, hy]
  have hyp : leechIntegralPairing leechNormSixHS100Root.val
      (leechIntegralAction e y).val = 16 := by
    rw [← he, leechRootedA2_integral_pairing_action, hxy]
  obtain ⟨c, hcx, hcy⟩ := leechNormSixActualPair_transport leechNormSixHS100Root
    (leechIntegralAction e y) leechNormSixHS100Companion leechNormSixHS100Root_square
    hys leechNormSixHS100Companion_square hyp leechNormSixHS100Flag_pairing
  refine ⟨c * e, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, he, hcx]
  · rw [map_mul, LinearEquiv.mul_apply, hcy]

/-- Genuine flag transport is an equivalence of the complete original physical point sets. -/
theorem leechNormSixHS100Points_equiv (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16) :
    Nonempty (LeechNormSixHS100Points x y ≃
      LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) := by
  obtain ⟨g, hgx, hgy⟩ := leechNormSixHS100Flag_transport x y hx hy hxy
  have e := leechNormSixHS100PointsActionEquiv g x y
  rw [hgx, hgy] at e
  exact ⟨e⟩

/-- Every actual transported flag retains exactly the canonical point-set cardinality. -/
theorem leechNormSixHS100Points_card_transport (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hxy : leechIntegralPairing x.val y.val = 16) :
    Nat.card (LeechNormSixHS100Points x y) =
      Nat.card (LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion) := by
  obtain ⟨e⟩ := leechNormSixHS100Points_equiv x y hx hy hxy
  exact Nat.card_congr e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
