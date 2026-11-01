/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The explicit finite commutator bound gives the central two-element extension structure. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalBinaryAction
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Under the explicit source bound, every source commutator element has square one. -/
theorem co1Universal_commutator_square_of_card_le_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x : commutator Co1UniversalPresentation) : x ^ 2 = 1 := by
  have : Finite (commutator Co1UniversalPresentation) := hfinite
  have hpos : 0 < Nat.card (commutator Co1UniversalPresentation) := Nat.card_pos
  have hcases : Nat.card (commutator Co1UniversalPresentation) = 1 ∨
      Nat.card (commutator Co1UniversalPresentation) = 2 := by omega
  rcases hcases with h | h
  · have hx := pow_card_eq_one' (x := x)
    rw [h, pow_one] at hx
    rw [hx]
    exact one_pow _
  · simpa only [h] using (pow_card_eq_one' (x := x))

/-- If the bounded source commutator is nontrivial, its exact order is two. -/
theorem co1Universal_commutator_card_eq_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Nat.card (commutator Co1UniversalPresentation) = 2 := by
  have : Finite (commutator Co1UniversalPresentation) := hfinite
  have hpos : 0 < Nat.card (commutator Co1UniversalPresentation) := Nat.card_pos
  have hnotone : Nat.card (commutator Co1UniversalPresentation) ≠ 1 := by
    intro h
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact hz ((Nat.card_eq_one_iff_unique.mp h).1.elim z 1)
  omega

/-- The nontrivial bounded source commutator has one unique nonidentity involution. -/
theorem co1Universal_commutator_unique_involution
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    ∃! z : commutator Co1UniversalPresentation, z ≠ 1 ∧ z ^ 2 = 1 := by
  have he := co1Universal_commutator_card_eq_two hfinite hcard hne
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : commutator Co1UniversalPresentation)).mp he
  refine ⟨z, ⟨hz, co1Universal_commutator_square_of_card_le_two hfinite hcard z⟩, ?_⟩
  exact fun y hy => hu y hy.1

/-- Normality makes a source commutator of order at most two central in the whole source group. -/
theorem co1Universal_commutator_le_center_of_card_le_two
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    commutator Co1UniversalPresentation ≤ Subgroup.center Co1UniversalPresentation := by
  intro x hx
  by_cases hone : x = 1
  · rw [hone]
    exact Subgroup.one_mem _
  have hne : commutator Co1UniversalPresentation ≠ ⊥ := by
    intro h
    rw [h] at hx
    exact hone (Subgroup.mem_bot.mp hx)
  have he := co1Universal_commutator_card_eq_two hfinite hcard hne
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : commutator Co1UniversalPresentation)).mp he
  let c : commutator Co1UniversalPresentation := ⟨x, hx⟩
  have hc : c ≠ 1 := fun h => hone (congrArg Subtype.val h)
  have hc' := hu c hc
  apply Subgroup.mem_center_iff.mpr
  intro g
  let d : commutator Co1UniversalPresentation := ⟨g * x * g⁻¹,
    (inferInstance : (commutator Co1UniversalPresentation).Normal).conj_mem x hx g⟩
  have hd : d ≠ 1 := by
    intro h
    apply hone
    exact conj_eq_one_iff.mp (congrArg Subtype.val h)
  have hd' := hu d hd
  have hconj : g * x * g⁻¹ = x := congrArg Subtype.val (hd'.trans hc'.symm)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun y => y * g) hconj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
