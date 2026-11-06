/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Conway quotient action on short labels and its counting identity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderFrameCount

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual short-label permutation action descends through the central lattice signs. -/
noncomputable def co1ShortPermutation : Co1 →* Equiv.Perm GriessShortIndex :=
  QuotientGroup.lift signsSubgroup griessShortPermutation (by
    intro e he
    change griessShortPermutation e = 1
    apply Equiv.ext
    intro r
    apply griessShortPermutation_binary_trivial
    have he' : e ∈ leechBinaryAction.ker := by rwa [leechBinaryAction_ker]
    exact he')

/-- Quotienting changes no actual permutation of the short labels. -/
theorem co1ShortPermutation_mk (e : leechIsomSubgroup) :
    co1ShortPermutation (QuotientGroup.mk e) = griessShortPermutation e :=
  QuotientGroup.lift_mk' signsSubgroup _ e

/-- Actual Co₁ acts on the dictionary labels for all short lattice classes. -/
noncomputable instance : MulAction Co1 GriessShortIndex where
  smul c r := co1ShortPermutation c r
  one_smul r := by
    change co1ShortPermutation 1 r = r
    rw [map_one]
    rfl
  mul_smul c d r := by
    change co1ShortPermutation (c * d) r = co1ShortPermutation c (co1ShortPermutation d r)
    rw [map_mul]
    rfl

/-- Transitivity of actual short-vector permutations identifies the whole Co₁ orbit. -/
theorem co1Short_orbit_eq_univ (r₀ : GriessShortIndex)
    (ht : ∀ r : GriessShortIndex, ∃ e : leechIsomSubgroup,
      griessShortPermutation e r₀ = r) : MulAction.orbit Co1 r₀ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro r
  obtain ⟨e, he⟩ := ht r
  refine ⟨QuotientGroup.mk e, ?_⟩
  change co1ShortPermutation (QuotientGroup.mk e) r₀ = r
  rw [co1ShortPermutation_mk]
  exact he

/-- Actual short transitivity supplies the 98280-to-one Co₁ stabilizer count.
Transitivity remains an explicit geometric input in this helper. -/
theorem co1Short_card_mul_stabilizer (r₀ : GriessShortIndex)
    (ht : ∀ r : GriessShortIndex, ∃ e : leechIsomSubgroup,
      griessShortPermutation e r₀ = r) :
    98280 * Nat.card (MulAction.stabilizer Co1 r₀) = Nat.card Co1 := by
  have : Finite Co1 := co1_finite
  let _ := Fintype.ofFinite Co1
  let _ := Fintype.ofFinite (MulAction.orbit Co1 r₀)
  let _ := Fintype.ofFinite (MulAction.stabilizer Co1 r₀)
  have horbit : Nat.card (MulAction.orbit Co1 r₀) = 98280 := by
    rw [co1Short_orbit_eq_univ r₀ ht]
    rw [Nat.card_congr (Equiv.Set.univ GriessShortIndex), Nat.card_eq_fintype_card]
    exact griessShortIndex_card
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group Co1 r₀
  simpa only [← Nat.card_eq_fintype_card, horbit] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
