/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-! # Pushout complements and their open subspaces

Let `f : S → X₁` and `g : S → X₂` be maps of sets. In any pushout of
this span, a point of `X₂` outside the image of `g` is identified neither
with another point of `X₂` nor with a point of `X₁`.

For a pushout square of topological spaces with maps `t : X₁ → X₂`,
`l : X₁ → X₃`, `r : X₂ → X₄` and `b : X₃ → X₄`, the map
`X₂ ⊕ X₃ → X₄` induced by `r` and `b` is a quotient map. If an open
set `U ⊆ X₄` has empty inverse image under `r` and its inverse image
under `b` avoids the image of `l`, then `b` restricts to a homeomorphism
from `b⁻¹(U)` to `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace CategoryTheory.Limits.Types

variable {S X₁ X₂ : Type u} {f : S ⟶ X₁} {g : S ⟶ X₂}

private theorem pushout_rel_notMem_range_invariant
    {x : X₂} (hx : x ∉ Set.range g) {a b : X₁ ⊕ X₂}
    (hab : Relation.EqvGen (Pushout.Rel f g) a b) :
    a = Sum.inr x ↔ b = Sum.inr x := by
  induction hab with
  | rel a b hab =>
      rcases hab with ⟨s⟩
      constructor
      · intro hbad
        cases hbad
      · intro hbad
        have : g s = x := Sum.inr.inj hbad
        exact (hx ⟨s, this⟩).elim
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem pushout_inr_injectiveOn_compl_range_aux
    {x y : X₂} (hx : x ∉ Set.range g)
    (h : Pushout.inr f g x = Pushout.inr f g y) : x = y := by
  have hEqv : Relation.EqvGen (Pushout.Rel f g)
      (Sum.inr x) (Sum.inr y) := Quot.eqvGen_exact h
  have hyx : Sum.inr y = Sum.inr x :=
    (pushout_rel_notMem_range_invariant hx hEqv).mp rfl
  exact Sum.inr.inj hyx.symm

private theorem pushout_inl_ne_inr_of_notMem_range_aux
    {z : X₁} {x : X₂} (hx : x ∉ Set.range g) :
    Pushout.inl f g z ≠ Pushout.inr f g x := by
  intro h
  have hEqv : Relation.EqvGen (Pushout.Rel f g)
      (Sum.inl z) (Sum.inr x) := Quot.eqvGen_exact h
  have hbad : Sum.inl z = Sum.inr x := (pushout_rel_notMem_range_invariant hx hEqv).mpr rfl
  cases hbad

/-- For maps `f : S → X₁` and `g : S → X₂`, let `c` be a pushout cocone
of their span. If `x ∈ X₂` does not lie in the image of `g`, then
`c.inr(x) = c.inr(y)` implies `x = y` for every `y ∈ X₂`. The condition
on the second point `y` is unrestricted. -/
theorem pushoutCocone_inr_eq_inr_of_notMem_range_of_isColimit
    {c : PushoutCocone f g} (hc : IsColimit c)
    {x y : X₂} (hx : x ∉ Set.range g) (hxy : c.inr x = c.inr y) : x = y := by
  let e : c ≅ Pushout.cocone f g :=
    IsColimit.uniqueUpToIso hc (Pushout.isColimitCocone f g)
  have hcanonical : Pushout.inr f g x = Pushout.inr f g y := by
    convert! congrArg e.hom.hom hxy
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.right).symm x
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.right).symm y
  exact pushout_inr_injectiveOn_compl_range_aux hx hcanonical

/-- For a pushout cocone of `f : S → X₁` and `g : S → X₂`, a point
`x ∈ X₂` outside the image of `g` has image distinct from the image of
every `z ∈ X₁`: `c.inl(z) ≠ c.inr(x)`. -/
theorem pushoutCocone_inl_ne_inr_of_notMem_range_of_isColimit
    {c : PushoutCocone f g} (hc : IsColimit c)
    {z : X₁} {x : X₂} (hx : x ∉ Set.range g) : c.inl z ≠ c.inr x := by
  intro hzx
  let e : c ≅ Pushout.cocone f g :=
    IsColimit.uniqueUpToIso hc (Pushout.isColimitCocone f g)
  have hcanonical : Pushout.inl f g z = Pushout.inr f g x := by
    convert! congrArg e.hom.hom hzx
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm z
    · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.right).symm x
  exact pushout_inl_ne_inr_of_notMem_range_aux (f := f) (g := g) hx hcanonical

/-- For a pushout cocone of `f : S → X₁` and `g : S → X₂`, the right
inclusion is injective on the complement of the image of `g` in `X₂`.
No injectivity assumption is imposed on either map of the original span. -/
theorem pushoutCocone_inr_injectiveOn_compl_range_of_isColimit
    {c : PushoutCocone f g} (hc : IsColimit c) :
    Set.InjOn c.inr (Set.range g)ᶜ := by
  intro x hx y _ hxy
  exact pushoutCocone_inr_eq_inr_of_notMem_range_of_isColimit hc hx hxy

end CategoryTheory.Limits.Types

namespace TopCat

variable {X₁ X₂ X₃ X₄ : TopCat.{u}}
variable {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
variable {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- Suppose `t : X₁ → X₂`, `l : X₁ → X₃`, `r : X₂ → X₄` and
`b : X₃ → X₄` form a pushout square of topological spaces. The induced
map `X₂ ⊕ X₃ → X₄`, equal to `r` on the first summand and to `b` on
the second, is a quotient map. Thus it is surjective, and a subset of
`X₄` is open exactly when its inverse images under both maps are open. -/
theorem isQuotientMap_sumElim_of_isPushout
    (h : IsPushout t l r b) :
    IsQuotientMap (Sum.elim r b : X₂ ⊕ X₃ → X₄) := by
  rw [isQuotientMap_iff]
  refine ⟨(isCoinducing_iff).2 (fun U ↦ ?_), ?_⟩
  · rw [isOpen_sum_iff]
    change (IsOpen (r ⁻¹' U) ∧ IsOpen (b ⁻¹' U)) ↔ IsOpen U
    constructor
    · rintro ⟨hr, hb⟩
      have hcolim : IsOpen U ↔
          ∀ j, IsOpen (h.cocone.ι.app j ⁻¹' U) :=
        TopCat.isOpen_iff_of_isColimit h.cocone h.isColimit U
      rw [hcolim]
      rintro (_ | _ | _)
      · exact hr.preimage t.hom.continuous
      · exact hr
      · exact hb
    · intro hU
      exact ⟨hU.preimage r.hom.continuous, hU.preimage b.hom.continuous⟩
  · intro x
    obtain hx | hx := CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
      (h.map (forget TopCat)) x
    · obtain ⟨y, rfl⟩ := hx
      exact ⟨Sum.inl y, rfl⟩
    · obtain ⟨y, rfl⟩ := hx
      exact ⟨Sum.inr y, rfl⟩

/-- Let `t : X₁ → X₂`, `l : X₁ → X₃`, `r : X₂ → X₄` and
`b : X₃ → X₄` form a pushout square of topological spaces. Suppose
`U ⊆ X₄` is open, `r⁻¹(U)` is empty, and `b⁻¹(U)` is disjoint from
the image of `l`. Then the restriction `b⁻¹(U) → U` is a homeomorphism,
where both spaces carry their subspace topologies. -/
theorem isHomeomorph_restrictPreimage_inr_of_isPushout
    (h : IsPushout t l r b) {U : Set X₄} (hU : IsOpen U)
    (hr : r ⁻¹' U = ∅) (hl : b ⁻¹' U ⊆ (Set.range l)ᶜ) :
    IsHomeomorph (U.restrictPreimage b) := by
  let hType := h.map (forget TopCat)
  have hS : IsOpen (b ⁻¹' U) := hU.preimage b.hom.continuous
  have hinj : Function.Injective (U.restrictPreimage b) := by
    intro x y hxy
    apply Subtype.ext
    apply Types.pushoutCocone_inr_eq_inr_of_notMem_range_of_isColimit
      hType.isColimit (hl x.prop)
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective (U.restrictPreimage b) := by
    intro y
    obtain hy | hy := CategoryTheory.Limits.Types.eq_or_eq_of_isPushout hType y.val
    · obtain ⟨x, hx⟩ := hy
      have hx' : r x = y.val := by simpa using hx
      have hxU : x ∈ r ⁻¹' U := by
        change r x ∈ U
        rw [hx']
        exact y.prop
      rw [hr] at hxU
      exact hxU.elim
    · obtain ⟨x, hx⟩ := hy
      have hx' : b x = y.val := by simpa using hx
      have hxU : x ∈ b ⁻¹' U := by
        change b x ∈ U
        rw [hx']
        exact y.prop
      refine ⟨⟨x, hxU⟩, ?_⟩
      apply Subtype.ext
      exact hx'
  have hopen : IsOpenMap (U.restrictPreimage b) := by
    intro A hA
    let A' : Set X₃ := Subtype.val '' A
    have hA'_open : IsOpen A' :=
      hS.isOpenEmbedding_subtypeVal.isOpenMap A hA
    have hA'_sub : A' ⊆ b ⁻¹' U := by
      rintro x ⟨a, _, rfl⟩
      exact a.prop
    let V : Set X₄ := b '' A'
    have hrV : r ⁻¹' V = ∅ := by
      ext z
      constructor
      · rintro ⟨x, hxA, hxb⟩
        have hxnot : x ∉ Set.range l := hl (hA'_sub hxA)
        have hne := Types.pushoutCocone_inl_ne_inr_of_notMem_range_of_isColimit
          hType.isColimit (z := z) (x := x) hxnot
        exact (hne hxb.symm).elim
      · intro hz
        exact hz.elim
    have hbV : b ⁻¹' V = A' := by
      ext z
      constructor
      · rintro ⟨x, hxA, hxb⟩
        have hxnot : x ∉ Set.range l := hl (hA'_sub hxA)
        have hxz := Types.pushoutCocone_inr_eq_inr_of_notMem_range_of_isColimit
          hType.isColimit hxnot hxb
        simpa [hxz] using hxA
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hV : IsOpen V := by
      have hcolim : IsOpen V ↔
          ∀ j, IsOpen (h.cocone.ι.app j ⁻¹' V) :=
        TopCat.isOpen_iff_of_isColimit h.cocone h.isColimit V
      rw [hcolim]
      rintro (_ | _ | _)
      · change IsOpen (t ⁻¹' (r ⁻¹' V))
        rw [hrV, Set.preimage_empty]
        exact isOpen_empty
      · change IsOpen (r ⁻¹' V)
        rw [hrV]
        exact isOpen_empty
      · change IsOpen (b ⁻¹' V)
        rw [hbV]
        exact hA'_open
    have himage : Subtype.val '' (U.restrictPreimage b '' A) = V := by
      ext z
      constructor
      · rintro ⟨y, ⟨x, hxA, hxy⟩, hyz⟩
        refine ⟨x.val, ⟨x, hxA, rfl⟩, ?_⟩
        exact (congrArg Subtype.val hxy).trans hyz
      · rintro ⟨z, ⟨x, hxA, hxz⟩, hzb⟩
        subst z
        refine ⟨U.restrictPreimage b x, ⟨x, hxA, rfl⟩, ?_⟩
        exact hzb
    rw [hU.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
    rw [himage]
    exact hV
  exact ⟨(b.hom.restrictPreimage U).continuous, hopen, ⟨hinj, hsurj⟩⟩

end TopCat
