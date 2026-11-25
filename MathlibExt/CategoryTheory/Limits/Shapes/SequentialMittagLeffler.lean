/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Mittag--Leffler inverse sequences

This file specializes Mathlib's `Functor.IsMittagLeffler` to inverse
sequences.  It gives the numerical range-stabilization criterion, invariance
under natural isomorphism, an eventually-surjective criterion, and existence
of a section for levelwise-nonempty Type-valued towers.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory Opposite Set

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- A concrete inverse sequence is sequentially Mittag--Leffler when its
underlying Type-valued functor is Mittag--Leffler. -/
abbrev IsSequentialMittagLeffler (F : ℕᵒᵖ ⥤ C) : Prop :=
  (F ⋙ forget C).IsMittagLeffler

/-- For an inverse sequence, the Mittag--Leffler condition is equivalent to
eventual stabilization of the ranges into every fixed level. -/
theorem isSequentialMittagLeffler_iff_range_stabilizes
    (F : ℕᵒᵖ ⥤ C) :
    F.IsSequentialMittagLeffler ↔
      ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, ∀ k : ℕ, ∀ hmk : m ≤ k,
        range ((F ⋙ forget C).map (homOfLE (hnm.trans hmk)).op) =
          range ((F ⋙ forget C).map (homOfLE hnm).op) := by
  let U := F ⋙ forget C
  constructor
  · intro h n
    obtain ⟨⟨m⟩, f, hf⟩ := h (op n)
    let hnm : n ≤ m := leOfHom f.unop
    have hf_eq : f = (homOfLE hnm).op := Subsingleton.elim _ _
    rw [hf_eq] at hf
    refine ⟨m, hnm, fun k hmk => Subset.antisymm ?_ (hf _)⟩
    rw [show (homOfLE (hnm.trans hmk)).op =
        (homOfLE hmk).op ≫ (homOfLE hnm).op by
      apply Subsingleton.elim]
    rw [U.map_comp, types_comp]
    exact range_comp_subset_range _ _
  · intro h
    change U.IsMittagLeffler
    rw [U.isMittagLeffler_iff_subset_range_comp]
    rintro ⟨n⟩
    obtain ⟨m, hnm, hm⟩ := h n
    let f : op m ⟶ op n := (homOfLE hnm).op
    refine ⟨op m, f, ?_⟩
    rintro ⟨k⟩ g
    let hmk : m ≤ k := leOfHom g.unop
    have hgf : g ≫ f = (homOfLE (hnm.trans hmk)).op :=
      Subsingleton.elim _ _
    rw [hgf, hm k hmk]

section Iso

variable {J : Type u} [Category.{v} J] {F G : J ⥤ Type w}

/-- The Mittag--Leffler condition is invariant under natural isomorphism. -/
theorem IsMittagLeffler.of_iso (h : F.IsMittagLeffler) (e : F ≅ G) :
    G.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := h j
  refine ⟨i, f, ?_⟩
  intro k g
  rintro y ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hf g ⟨e.inv.app i x, rfl⟩
  refine ⟨e.hom.app k z, ?_⟩
  calc
    G.map g (e.hom.app k z) = e.hom.app j (F.map g z) :=
      (ConcreteCategory.congr_hom (e.hom.naturality g) z).symm
    _ = e.hom.app j (F.map f (e.inv.app i x)) := congrArg _ hz
    _ = G.map f (e.hom.app i (e.inv.app i x)) :=
      ConcreteCategory.congr_hom (e.hom.naturality f) (e.inv.app i x)
    _ = G.map f x := by
      apply congrArg (G.map f)
      have he := ConcreteCategory.congr_hom (e.inv_hom_id_app i) x
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using he

/-- Naturally isomorphic Type-valued functors satisfy the Mittag--Leffler
condition simultaneously. -/
theorem isMittagLeffler_iff_of_iso (e : F ≅ G) :
    F.IsMittagLeffler ↔ G.IsMittagLeffler :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end Iso

section TypeTower

variable (F : ℕᵒᵖ ⥤ Type w)

/-- If the successor transitions are surjective from `N` onward, every
transition between stages at least `N` is surjective. -/
theorem surjective_map_of_eventually_surjective_transition
    {N m k : ℕ}
    (h : ∀ n : ℕ, N ≤ n → Function.Surjective
      (F.map (homOfLE (Nat.le_succ n)).op))
    (hNm : N ≤ m) (hmk : m ≤ k) :
    Function.Surjective (F.map (homOfLE hmk).op) := by
  induction k, hmk using Nat.le_induction with
  | base =>
      have heq : (homOfLE (Nat.le_refl m)).op = 𝟙 (op m) :=
        Subsingleton.elim _ _
      rw [heq, F.map_id]
      exact Function.surjective_id
  | succ k hmk ih =>
      have hs := h k (hNm.trans hmk)
      have heq : (homOfLE (Nat.le.step hmk)).op =
          (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hmk).op :=
        Subsingleton.elim _ _
      rw [heq, F.map_comp, types_comp]
      exact ih.comp hs

/-- If all successor transitions of an inverse sequence are surjective from
some point onward, then the sequence is Mittag--Leffler. -/
theorem isMittagLeffler_of_eventually_surjective_transition
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (F.map (homOfLE (Nat.le_succ n)).op)) :
    F.IsMittagLeffler := by
  obtain ⟨N, hN⟩ := h
  rw [F.isMittagLeffler_iff_subset_range_comp]
  rintro ⟨n⟩
  let m := max n N
  have hnm : n ≤ m := le_max_left _ _
  have hNm : N ≤ m := le_max_right _ _
  let f : op m ⟶ op n := (homOfLE hnm).op
  refine ⟨op m, f, ?_⟩
  rintro ⟨k⟩ g
  let hmk : m ≤ k := leOfHom g.unop
  have hg : g = (homOfLE hmk).op := Subsingleton.elim _ _
  rw [hg]
  rintro y ⟨x, rfl⟩
  obtain ⟨z, hz⟩ :=
    F.surjective_map_of_eventually_surjective_transition hN hNm hmk x
  refine ⟨z, ?_⟩
  simpa only [F.map_comp, types_comp, comp_apply] using congrArg (F.map f) hz

/-- A levelwise-nonempty Mittag--Leffler inverse sequence of types has a
compatible section. -/
theorem nonempty_sections_of_isMittagLeffler
    (h : F.IsMittagLeffler) [∀ j : ℕᵒᵖ, Nonempty (F.obj j)] :
    Nonempty F.sections := by
  let R := F.toEventualRanges
  let t (n : ℕ) : R.obj (op (n + 1)) → R.obj (op n) :=
    R.map (homOfLE (Nat.le_succ n)).op
  have ht (n : ℕ) : Function.Surjective (t n) :=
    F.surjective_toEventualRanges h (homOfLE (Nat.le_succ n)).op
  have hR0 : Nonempty (R.obj (op 0)) :=
    F.toEventualRanges_nonempty h (op 0)
  let prev (n : ℕ) (x : R.obj (op n)) : R.obj (op (n + 1)) :=
    Classical.choose (ht n x)
  have hprev (n : ℕ) (x : R.obj (op n)) : t n (prev n x) = x :=
    Classical.choose_spec (ht n x)
  let x : (n : ℕ) → R.obj (op n) := fun n =>
    Nat.rec (motive := fun n => R.obj (op n))
      (Classical.choice hR0) (fun n xn => prev n xn) n
  have hx (n : ℕ) : t n (x (n + 1)) = x n := by
    change t n (prev n (x n)) = x n
    exact hprev n (x n)
  let K : ℕᵒᵖ ⥤ Type w := (Functor.const ℕᵒᵖ).obj PUnit
  let τ : K ⟶ R :=
    NatTrans.ofOpSequence (fun n => ↾(fun _ : PUnit => x n)) (fun n => by
      apply ConcreteCategory.hom_ext
      intro _
      exact (hx n).symm)
  let s : R.sections :=
    ⟨fun j => τ.app j PUnit.unit, fun {i j} f => by
      have hτ := ConcreteCategory.congr_hom (τ.naturality f) PUnit.unit
      have hK : K.map f PUnit.unit = PUnit.unit := by
        dsimp only [K]
        change PUnit.unit = PUnit.unit
        rfl
      calc
        R.map f (τ.app i PUnit.unit) =
            τ.app j (K.map f PUnit.unit) := hτ.symm
        _ = τ.app j PUnit.unit := congrArg (τ.app j) hK⟩
  exact ⟨F.toEventualRangesSectionsEquiv s⟩

end TypeTower

end CategoryTheory.Functor

end
