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
# Mittag–Leffler inverse sequences and compatible sections

For a concrete inverse tower F, the sequential Mittag–Leffler condition is eventual
stabilization of the ranges into each fixed level: for every n, some m ≥ n has Im(F_k → F_n) =
Im(F_m → F_n) for all k ≥ m. It is the Mittag–Leffler condition on the underlying Type-valued
functor and is invariant under natural isomorphism.

For towers of types, successor maps that are surjective from a fixed stage onward imply this
condition. A Mittag–Leffler tower whose levels are all nonempty has a compatible section. The
section is constructed recursively in the stabilized ranges. Concrete carrier, object and
morphism universes remain independent.
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

/-- Mittag–Leffler condition for a concrete inverse tower.

For F : ℕᵒᵖ ⥤ C in a concrete category, IsSequentialMittagLeffler F means that F followed by
the forgetful functor to types is Mittag–Leffler. Equivalently, the ranges of maps from later
stages into each fixed stage eventually stabilize. -/
abbrev IsSequentialMittagLeffler (F : ℕᵒᵖ ⥤ C) : Prop :=
  (F ⋙ forget C).IsMittagLeffler

/-- Range-stabilization criterion for a concrete tower.

A concrete inverse tower F is sequentially Mittag–Leffler exactly when, for every n, there is
m ≥ n such that Im(F_k → F_n) = Im(F_m → F_n) for all k ≥ m. The images are ranges of the
underlying functions of the tower maps. -/
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

/-- Transport of the Mittag–Leffler condition by natural isomorphism.

For Type-valued functors F,G on any category J, a natural isomorphism e : F ≅ G carries a
Mittag–Leffler condition on F to one on G. Its component bijections identify the relevant
ranges and commute with every transition map. -/
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

/-- Equivalence of Mittag–Leffler conditions under natural isomorphism.

For Type-valued functors F,G on any category J and a natural isomorphism F ≅ G, F is
Mittag–Leffler if and only if G is Mittag–Leffler. -/
theorem isMittagLeffler_iff_of_iso (e : F ≅ G) :
    F.IsMittagLeffler ↔ G.IsMittagLeffler :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end Iso

section TypeTower

variable (F : ℕᵒᵖ ⥤ Type w)

/-- Surjectivity of all transitions beyond a surjective tail.

Let F be an inverse tower of types and suppose every successor transition F_{n+1} → F_n is
surjective for n ≥ N. If N ≤ m ≤ k, then the transition F_k → F_m is surjective, since it is a
finite composite of such successor maps. -/
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

/-- Mittag–Leffler condition from eventual successor surjectivity.

For an inverse tower of types, if there exists N such that every F_{n+1} → F_n is surjective
for n ≥ N, the tower is Mittag–Leffler. Into a fixed level n, ranges stabilize after max(n,N). -/
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

/-- Compatible section of a nonempty Mittag–Leffler tower.

Let F be a Mittag–Leffler inverse tower of types whose every level is nonempty. Then there
exists a family x_n ∈ F_n satisfying F_{n+1} → F_n on x_{n+1} equals x_n, and hence a section
of the full tower. Recursion in the nonempty stabilized ranges provides the family. -/
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
