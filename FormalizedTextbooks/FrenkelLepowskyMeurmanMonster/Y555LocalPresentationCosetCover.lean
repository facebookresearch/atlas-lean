/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite actual right-coset covers from a checked transition table for source involutions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetRelation
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Group generators that are involutions also generate the entire group as a monoid. -/
theorem y555Submonoid_closure_of_involutions {A G : Type*} [Group G] (values : A → G)
    (hsq : ∀ a, values a ^ 2 = 1)
    (hgen : Subgroup.closure (Set.range values) = ⊤) :
    Submonoid.closure (Set.range values) = ⊤ := by
  let P : Submonoid G := Submonoid.closure (Set.range values)
  have hinv : ∀ x ∈ P, x⁻¹ ∈ P := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have hi : (values a)⁻¹ = values a :=
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq a)
      rw [hi]
      exact Submonoid.subset_closure ⟨a, rfl⟩
    | one => simpa only [inv_one] using P.one_mem
    | mul x y hx hy ihx ihy =>
      rw [mul_inv_rev]
      exact P.mul_mem ihy ihx
  let K : Subgroup G :=
    { carrier := {x | x ∈ P}
      one_mem' := P.one_mem
      mul_mem' := by intro x y hx hy; exact P.mul_mem hx hy
      inv_mem' := by intro x hx; exact hinv x hx }
  have hle : Subgroup.closure (Set.range values) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact Submonoid.subset_closure hx
  rw [hgen] at hle
  apply top_unique
  intro x _
  exact hle (Subgroup.mem_top x)

/-- Proved source transitions supply an actual coset representative for every group element. -/
theorem y555CosetCover_of_transitions {A G : Type*} [Group G] {n : ℕ}
    (values : A → G) (hsq : ∀ a, values a ^ 2 = 1)
    (hgen : Subgroup.closure (Set.range values) = ⊤) (H : Subgroup G)
    (representatives : Fin n → G) (root : Fin n) (hroot : representatives root = 1)
    (next : Fin n → A → Fin n)
    (hnext : ∀ i a, y522CosetRelation H (representatives i * values a)
      (representatives (next i a))) (x : G) :
    ∃ i, y522CosetRelation H x (representatives i) := by
  have hmono := y555Submonoid_closure_of_involutions values hsq hgen
  refine Submonoid.induction_of_closure_eq_top_right
    (motive := fun z => ∃ i : Fin n, y522CosetRelation H z (representatives i))
    hmono x ?_ ?_
  · refine ⟨root, ?_⟩
    rw [hroot]
    exact y522CosetRelation_refl H 1
  · intro z y hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨i, hi⟩ := hz
    exact ⟨next i a, y522CosetRelation_trans H
      (y522CosetRelation_right H hi (values a)) (hnext i a)⟩

/-- A finite actual subgroup and its finite coset cover bound the genuine whole group order. -/
theorem y555Finite_card_of_cosetCover {G : Type*} [Group G] {n : ℕ}
    (H : Subgroup G) [Finite H] (representatives : Fin n → G)
    (hcover : ∀ x, ∃ i, y522CosetRelation H x (representatives i)) :
    Finite G ∧ Nat.card G ≤ Nat.card H * n := by
  let f : H × Fin n → G := fun p => p.1.val * representatives p.2
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨(⟨x * (representatives i)⁻¹, hi⟩, i), ?_⟩
    simp only [f, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨Finite.of_surjective f hsurj, ?_⟩
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective f hsurj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
