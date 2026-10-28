/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ShortAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivity

/-! Counting the actual short-label stabilizer inside the concrete Conway quotient.
The conventional Co₂ order is obtained conditionally on the numeric Co₁ order.
No abstract Co₂ recognition or global Monster centralizer is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual subgroup of the concrete Co₁ quotient fixing a short lattice class. -/
noncomputable def co2ShortStabilizer (r : GriessShortIndex) : Subgroup Co1 :=
  MulAction.stabilizer Co1 r

/-- Concrete Golay and ξ transitivity fills the entire actual quotient orbit. -/
theorem co2Short_orbit_eq_univ (r : GriessShortIndex) :
    MulAction.orbit Co1 r = Set.univ := by
  apply co1Short_orbit_eq_univ r
  intro s
  obtain ⟨e, _, he⟩ := leechShort_concrete_label_transitive r s
  exact ⟨e, he⟩

/-- Every actual short stabilizer has index 98280. -/
theorem co2Short_stabilizer_index (r : GriessShortIndex) :
    (co2ShortStabilizer r).index = 98280 := by
  rw [co2ShortStabilizer, MulAction.index_stabilizer, ← Nat.card_coe_set_eq,
    co2Short_orbit_eq_univ, Nat.card_congr (Equiv.Set.univ GriessShortIndex),
    Nat.card_eq_fintype_card]
  exact griessShortIndex_card

/-- Unconditional order relation for the actual subgroup fixing a short class. -/
theorem co2Short_card_relation (r : GriessShortIndex) :
    98280 * Nat.card (co2ShortStabilizer r) = Nat.card Co1 := by
  apply co1Short_card_mul_stabilizer r
  intro s
  obtain ⟨e, _, he⟩ := leechShort_concrete_label_transitive r s
  exact ⟨e, he⟩

/-- The conventional numeric order follows once the actual Co₁ numeric count is proved. -/
theorem co2Short_card_of_co1_card (r : GriessShortIndex)
    (hCo1 : Nat.card Co1 = 4157776806543360000) :
    Nat.card (co2ShortStabilizer r) = 42305421312000 := by
  have h := co2Short_card_relation r
  rw [hCo1] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
