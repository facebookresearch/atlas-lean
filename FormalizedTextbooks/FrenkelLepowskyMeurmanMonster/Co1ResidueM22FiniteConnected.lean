/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FinitePredicates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FinitePathsData
public import Mathlib.Logic.Relation

/-! The cached parent trees certify connectivity in the original Golay hexad geometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem tree_reachable {P : Type*} {n : Nat} (r : P → P → Prop)
    (f : Fin (n + 1) → P) (parent : Fin (n + 1) → Fin (n + 1))
    (hparent : ∀ k, k.val ≠ 0 → (parent k).val < k.val ∧ r (f (parent k)) (f k)) :
    ∀ k, Relation.ReflTransGen r (f 0) (f k) := by
  have aux : ∀ m : Nat, ∀ k : Fin (n + 1), k.val = m →
      Relation.ReflTransGen r (f 0) (f k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk
      by_cases hz : k.val = 0
      · have he : k = 0 := Fin.ext hz
        rw [he]
      · obtain ⟨hp, he⟩ := hparent k hz
        exact (ih (parent k).val (by omega) (parent k) rfl).tail he
  exact fun k => aux k.val k rfl

private theorem reverse_path {P : Type*} {r : P → P → Prop}
    (hs : ∀ x y, r x y → r y x) {x y : P} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact ih.head (hs _ _ he)

/-- The actual auxiliary M22 distant graph is symmetric. -/
theorem co1ResidueM22Distant_symm (p q : Fin 24) (s t : Co1ResidueM22Point p q)
    (h : co1ResidueM22Distant p q s t) : co1ResidueM22Distant p q t s := by
  refine ⟨h.1.symm, ?_⟩
  rintro ⟨o, hp, hq, ht, hs⟩
  exact h.2 ⟨o, hp, hq, hs, ht⟩

/-- Every actual auxiliary M22 point is reached from the base by genuine distant edges. -/
theorem co1ResidueM22Finite_global_reached (s : Co1ResidueM22Point 0 1) :
    Relation.ReflTransGen (co1ResidueM22Distant 0 1) (co1ResidueM22FinitePoint 0) s := by
  have ht := tree_reachable (co1ResidueM22Distant 0 1)
    (fun k : Fin 231 => co1ResidueM22FinitePoint (co1ResidueM22GlobalOrder k))
    co1ResidueM22GlobalParent (fun k hk => by
      obtain ⟨hp, he⟩ := co1ResidueM22GlobalParent_edges k hk
      exact ⟨hp, (co1ResidueM22FiniteDistant_iff _ _).mp he⟩)
  obtain ⟨i, hi⟩ := co1ResidueM22FinitePoint_surjective s
  obtain ⟨k, hk⟩ := co1ResidueM22GlobalOrder_bijective.2 i
  have h := ht k
  rwa [co1ResidueM22GlobalOrder_zero, hk, hi] at h

/-- The original Golay hexad distant graph on all 231 points is connected. -/
theorem co1ResidueM22Finite_global_connected (s t : Co1ResidueM22Point 0 1) :
    Relation.ReflTransGen (co1ResidueM22Distant 0 1) s t :=
  (reverse_path (co1ResidueM22Distant_symm 0 1)
    (co1ResidueM22Finite_global_reached s)).trans (co1ResidueM22Finite_global_reached t)

/-- The literal local tree addresses denote actual distant neighbors of the base point. -/
def co1ResidueM22FiniteLocalPoint (k : Fin 160) :
    {s : Co1ResidueM22Point 0 1 // co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) s} :=
  ⟨co1ResidueM22FinitePoint (co1ResidueM22LocalOrder k),
    (co1ResidueM22FiniteDistant_iff _ _).mp
      ((co1ResidueM22LocalOrder_covers _).mpr ⟨k, rfl⟩)⟩

/-- Every actual distant neighbor occurs in the local tree enumeration. -/
theorem co1ResidueM22FiniteLocalPoint_surjective :
    Function.Surjective co1ResidueM22FiniteLocalPoint := by
  intro s
  obtain ⟨i, hi⟩ := co1ResidueM22FinitePoint_surjective s.val
  have hd : co1ResidueM22FiniteDistant 0 i = true :=
    (co1ResidueM22FiniteDistant_iff _ _).mpr (hi.symm ▸ s.property)
  obtain ⟨k, hk⟩ := (co1ResidueM22LocalOrder_covers i).mp hd
  refine ⟨k, Subtype.ext ?_⟩
  change co1ResidueM22FinitePoint (co1ResidueM22LocalOrder k) = s.val
  rw [hk, hi]

/-- Connectivity inside the base distant-neighbor set uses genuine hexad lines
whose third point is nearby the base. -/
theorem co1ResidueM22Finite_local_base_connected
    (s t : {s : Co1ResidueM22Point 0 1 //
      co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) s}) :
    Relation.ReflTransGen (fun s t => ∃ w,
      (co1ResidueM22Line 0 1 s.val t.val w ∨ co1ResidueM22Line 0 1 t.val s.val w) ∧
      ¬ co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) w) s t := by
  let r := fun s t : {s : Co1ResidueM22Point 0 1 //
      co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) s} => ∃ w,
      (co1ResidueM22Line 0 1 s.val t.val w ∨ co1ResidueM22Line 0 1 t.val s.val w) ∧
      ¬ co1ResidueM22Distant 0 1 (co1ResidueM22FinitePoint 0) w
  have ht := tree_reachable r co1ResidueM22FiniteLocalPoint co1ResidueM22LocalParent
    (fun k hk => by
      obtain ⟨hp, he, hn⟩ := co1ResidueM22LocalParent_edges k hk
      refine ⟨hp, co1ResidueM22FinitePoint (co1ResidueM22LocalThird k), Or.inl ?_, ?_⟩
      · exact co1ResidueM22FiniteLine_of_masks _ _ _ _ he
      · intro hd
        have hh := (co1ResidueM22FiniteDistant_iff _ _).mpr hd
        rw [hn] at hh
        exact Bool.noConfusion hh)
  have hs : ∀ u, Relation.ReflTransGen r (co1ResidueM22FiniteLocalPoint 0) u := by
    intro u
    obtain ⟨k, rfl⟩ := co1ResidueM22FiniteLocalPoint_surjective u
    exact ht k
  exact (reverse_path (fun u v ⟨w, hline, hn⟩ => ⟨w, hline.symm, hn⟩) (hs s)).trans (hs t)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
