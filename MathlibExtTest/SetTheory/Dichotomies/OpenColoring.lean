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

public import MathlibExt.SetTheory.Dichotomies.OpenColoring
public import Mathlib.Topology.Bases

@[expose] public section

namespace MathlibExtTest.SetTheory.Dichotomies.OpenColoring

open MetaMathlibExt

-- Logic 335: Open Coloring

/-- **Not vacuous**: the empty colouring qualifies. -/

theorem isOpenColoring_empty {X : Type} [TopologicalSpace X] :
    IsOpenColoring (∅ : Set (X × X)) where
  isOpen := isOpen_empty
  symm := fun _ _ h => absurd h (by simp)
  irrefl := fun _ => by simp

/-- **Proper**: `Set.univ` fails irreflexivity as soon as `X` is inhabited, so the predicate is
not satisfied by everything. -/

theorem not_isOpenColoring_univ {X : Type} [TopologicalSpace X] (x : X) :
    ¬ IsOpenColoring (Set.univ : Set (X × X)) :=
  fun h => h.irrefl x (Set.mem_univ _)

/-- Symmetry in the form used at point of use. -/

theorem IsOpenColoring.mem_comm {X : Type} [TopologicalSpace X] {K : Set (X × X)}
    (h : IsOpenColoring K) {x y : X} : (x, y) ∈ K ↔ (y, x) ∈ K :=
  ⟨h.symm x y, h.symm y x⟩

/-- Irreflexivity in the form used at point of use: `K` misses the diagonal. -/

theorem IsOpenColoring.ne_of_mem {X : Type} [TopologicalSpace X] {K : Set (X × X)}
    (h : IsOpenColoring K) {x y : X} (hxy : (x, y) ∈ K) : x ≠ y := by
  rintro rfl
  exact h.irrefl x hxy

-- Logic 337: $K$-homogeneous

/-- Homogeneity passes to subsets, so the content lives in the size demanded of `H`. -/

theorem _root_.MetaMathlibExt.IsColoringHomogeneous.mono {X : Type} {K : Set (X × X)} {H H' : Set X} (hsub : H' ⊆ H)
    (h : IsColoringHomogeneous K H) : IsColoringHomogeneous K H' :=
  Set.Pairwise.mono hsub h

/-- **The uncountability demand is load-bearing**: every subsingleton is homogeneous, for every
colouring. -/

theorem isColoringHomogeneous_subsingleton {X : Type} (K : Set (X × X)) {H : Set X}
    (h : H.Subsingleton) : IsColoringHomogeneous K H :=
  fun _ hx _ hy hne => absurd (h hx hy) hne

/-- In particular `∅` is homogeneous. -/

theorem isColoringHomogeneous_empty {X : Type} (K : Set (X × X)) :
    IsColoringHomogeneous K (∅ : Set X) :=
  isColoringHomogeneous_subsingleton K Set.subsingleton_empty

/-- **Degenerate case**: the total colouring makes everything homogeneous. -/

theorem isColoringHomogeneous_univ {X : Type} (H : Set X) :
    IsColoringHomogeneous (Set.univ : Set (X × X)) H :=
  fun _ _ _ _ _ => Set.mem_univ _

-- Logic 338: $K$-free coloring

/-- Freeness passes to subsets. -/

theorem _root_.MetaMathlibExt.IsColoringFree.mono {X : Type} {K : Set (X × X)} {H H' : Set X} (hsub : H' ⊆ H)
    (h : IsColoringFree K H) : IsColoringFree K H' :=
  fun x hx y hy => h x (hsub hx) y (hsub hy)

/-- `∅` is free for every colouring. -/

theorem isColoringFree_empty {X : Type} (K : Set (X × X)) :
    IsColoringFree K (∅ : Set X) :=
  fun _ hx => absurd hx (by simp)

/-- **Degenerate case**: every set is free for the empty colouring, so the second alternative of
`OpenColoringAxiom` is satisfiable outright there. -/

theorem isColoringFree_of_empty_coloring {X : Type} (H : Set X) :
    IsColoringFree (∅ : Set (X × X)) H :=
  fun _ _ _ _ => by simp

-- Logic 339: Open Coloring Axiom

/-- **The alternatives are exclusive, step 1**: homogeneous and free forces a subsingleton. -/

theorem subsingleton_of_homogeneous_of_free {X : Type} {K : Set (X × X)} {S : Set X}
    (hhom : IsColoringHomogeneous K S) (hfree : IsColoringFree K S) : S.Subsingleton := by
  intro x hx y hy
  by_contra hne
  exact hfree x hx y hy (hhom hx hy hne)

/-- **The alternatives are exclusive.**  An uncountable homogeneous set cannot coexist with a
countable cover by free sets, so this is a real dichotomy and not a disjunction both sides can
satisfy. -/

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

/-- **Content only for uncountable `X`**: on a countable space the singleton cover already
witnesses the second alternative, so `OpenColoringAxiom` asserts nothing there. -/

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

/-- **Degenerate case**: for the empty colouring the second alternative holds with the constant
cover, so the axiom is satisfiable. -/

theorem openColoringAxiom_of_empty_coloring {X : Type} :
    ∃ F : ℕ → Set X, (⋃ n, F n) = Set.univ ∧
      ∀ n, IsColoringFree (∅ : Set (X × X)) (F n) := by
  refine ⟨fun _ => Set.univ, ?_, fun _ _ _ _ _ => by simp⟩
  exact Set.iUnion_const _

end MathlibExtTest.SetTheory.Dichotomies.OpenColoring

end
