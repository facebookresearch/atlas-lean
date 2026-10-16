/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Topology.Bases
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 335, Logic 337, Logic 338, Logic 339
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 335: Open Coloring
structure IsOpenColoring {X : Type} [TopologicalSpace X] (K : Set (X × X)) : Prop where
  isOpen : IsOpen K
  symm : ∀ x y : X, (x, y) ∈ K → (y, x) ∈ K
  irrefl : ∀ x : X, (x, x) ∉ K

theorem isOpenColoring_empty {X : Type} [TopologicalSpace X] :
    IsOpenColoring (∅ : Set (X × X)) where
  isOpen := isOpen_empty
  symm := fun _ _ h => absurd h (by simp)
  irrefl := fun _ => by simp

theorem not_isOpenColoring_univ {X : Type} [TopologicalSpace X] (x : X) :
    ¬ IsOpenColoring (Set.univ : Set (X × X)) :=
  fun h => h.irrefl x (Set.mem_univ _)

theorem IsOpenColoring.mem_comm {X : Type} [TopologicalSpace X] {K : Set (X × X)}
    (h : IsOpenColoring K) {x y : X} : (x, y) ∈ K ↔ (y, x) ∈ K :=
  ⟨h.symm x y, h.symm y x⟩

theorem IsOpenColoring.ne_of_mem {X : Type} [TopologicalSpace X] {K : Set (X × X)}
    (h : IsOpenColoring K) {x y : X} (hxy : (x, y) ∈ K) : x ≠ y := by
  rintro rfl
  exact h.irrefl x hxy

-- Logic 337: $K$-homogeneous
def IsColoringHomogeneous {X : Type} (K : Set (X × X)) (H : Set X) : Prop :=
  H.Pairwise fun x y => (x, y) ∈ K

theorem IsColoringHomogeneous.mono {X : Type} {K : Set (X × X)} {H H' : Set X} (hsub : H' ⊆ H)
    (h : IsColoringHomogeneous K H) : IsColoringHomogeneous K H' :=
  Set.Pairwise.mono hsub h

theorem isColoringHomogeneous_subsingleton {X : Type} (K : Set (X × X)) {H : Set X}
    (h : H.Subsingleton) : IsColoringHomogeneous K H :=
  fun _ hx _ hy hne => absurd (h hx hy) hne

theorem isColoringHomogeneous_empty {X : Type} (K : Set (X × X)) :
    IsColoringHomogeneous K (∅ : Set X) :=
  isColoringHomogeneous_subsingleton K Set.subsingleton_empty

theorem isColoringHomogeneous_univ {X : Type} (H : Set X) :
    IsColoringHomogeneous (Set.univ : Set (X × X)) H :=
  fun _ _ _ _ _ => Set.mem_univ _

-- Logic 338: $K$-free coloring
def IsColoringFree {X : Type} (K : Set (X × X)) (H : Set X) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, (x, y) ∉ K

theorem IsColoringFree.mono {X : Type} {K : Set (X × X)} {H H' : Set X} (hsub : H' ⊆ H)
    (h : IsColoringFree K H) : IsColoringFree K H' :=
  fun x hx y hy => h x (hsub hx) y (hsub hy)

theorem isColoringFree_empty {X : Type} (K : Set (X × X)) :
    IsColoringFree K (∅ : Set X) :=
  fun _ hx => absurd hx (by simp)

theorem isColoringFree_of_empty_coloring {X : Type} (H : Set X) :
    IsColoringFree (∅ : Set (X × X)) H :=
  fun _ _ _ _ => by simp

-- Logic 339: Open Coloring Axiom
def OpenColoringAxiom : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] (K : Set (X × X)),
    IsOpenColoring K →
      (∃ H : Set X, ¬ H.Countable ∧ IsColoringHomogeneous K H) ∨
      (∃ F : ℕ → Set X, (⋃ n, F n) = Set.univ ∧ ∀ n, IsColoringFree K (F n))

theorem subsingleton_of_homogeneous_of_free {X : Type} {K : Set (X × X)} {S : Set X}
    (hhom : IsColoringHomogeneous K S) (hfree : IsColoringFree K S) : S.Subsingleton := by
  intro x hx y hy
  by_contra hne
  exact hfree x hx y hy (hhom hx hy hne)

theorem not_homogeneous_and_free_cover {X : Type} {K : Set (X × X)} {H : Set X}
    (hH : ¬ H.Countable) (hhom : IsColoringHomogeneous K H)
    (F : ℕ → Set X) (hcov : (⋃ n, F n) = Set.univ) (hfree : ∀ n, IsColoringFree K (F n)) :
    False := by
  refine hH ?_
  have hsplit : H = ⋃ n, (H ∩ F n) := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  rw [hsplit]
  refine Set.countable_iUnion fun n => ?_
  refine Set.Subsingleton.countable (subsingleton_of_homogeneous_of_free (K := K) ?_ ?_)
  · exact fun _ hx _ hy hne => hhom hx.1 hy.1 hne
  · exact fun x hx y hy => hfree n x hx.2 y hy.2

theorem exists_free_cover_of_countable {X : Type} [TopologicalSpace X] [Countable X] [Nonempty X]
    {K : Set (X × X)} (hK : IsOpenColoring K) :
    ∃ F : ℕ → Set X, (⋃ n, F n) = Set.univ ∧ ∀ n, IsColoringFree K (F n) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat X
  refine ⟨fun n => {f n}, ?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := hf y
    exact ⟨n, hn.symm⟩
  · intro n p hp q hq
    rw [Set.mem_singleton_iff] at hp hq
    rw [hp, hq]
    exact hK.irrefl (f n)

theorem openColoringAxiom_of_empty_coloring {X : Type} :
    ∃ F : ℕ → Set X, (⋃ n, F n) = Set.univ ∧
      ∀ n, IsColoringFree (∅ : Set (X × X)) (F n) := by
  refine ⟨fun _ => Set.univ, ?_, fun _ _ _ _ _ => by simp⟩
  exact Set.iUnion_const _

end
