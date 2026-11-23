/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.CommSq

/-! # Binary gluing of continuous maps over a closed two-set cover

Given a `TopCat` object `X` with closed subsets `s` and `t` covering `X`,
and continuous maps `f` on `s` and `g` on `t` agreeing pointwise on the
overlap, there is a glued continuous map `F` on `X` restricting to `f`
and `g`.

Construction: define `F` pointwise by cases on `x ∈ s`, using the cover
to obtain `x ∈ t` in the complementary case; prove `ContinuousOn` on each
piece by comparing with `f` and `g` through `Set.domRestrict`, then glue
with `ContinuousOn.union_of_isClosed` and conclude with `continuousOn_univ`.
Restrictions are stated with `ContinuousMap.restrict`.

Nonclaims: no disk geometry, no path concatenation, no HELP statement, no
model-category instance, and no weak-equivalence conclusion.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace TopCat

/-- Binary gluing of continuous maps over a closed two-set cover.

Given closed `s` and `t` with `s ∪ t = univ` and maps `f` on `s`, `g` on
`t` agreeing pointwise on the overlap, there is `F` on `X` with
`F.restrict s = f` and `F.restrict t = g`. -/
theorem exists_continuousMap_glue_of_closed_cover
    {X : TopCat.{u}} {Z : TopCat.{v}} {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t)
    (hcover : s ∪ t = Set.univ)
    (f : ContinuousMap s Z) (g : ContinuousMap t Z)
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxt : x ∈ t),
      f ⟨x, hxs⟩ = g ⟨x, hxt⟩) :
    ∃ F : ContinuousMap X Z, F.restrict s = f ∧ F.restrict t = g := by
  classical
  set F0 : X → Z := fun x =>
    if hxs : x ∈ s then f ⟨x, hxs⟩
    else g ⟨x, by
      have hxU : x ∈ s ∪ t := by rw [hcover]; trivial
      rcases Set.mem_or_mem_of_mem_union hxU with h | h
      · exact absurd h hxs
      · exact h⟩ with hF0_def
  have hFs_pt : ∀ y : s, F0 (y : X) = f y := by
    intro y
    rw [hF0_def]
    simp only [dite_eq_left y.property]
  have hFt_pt : ∀ y : t, F0 (y : X) = g y := by
    intro y
    by_cases hxs : (y : X) ∈ s
    · rw [hF0_def]
      simp only [dite_eq_left hxs]
      have hxt : (y : X) ∈ t := y.property
      have h := hagree (y : X) hxs hxt
      have hy : (⟨(y : X), hxt⟩ : t) = y := Subtype.ext rfl
      rw [hy] at h
      exact h
    · rw [hF0_def]
      simp only [dite_eq_right hxs]
  have hFs : ContinuousOn F0 s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : s.domRestrict F0 = ⇑f := by
      funext y
      exact hFs_pt y
    rw [heq]
    exact f.continuous
  have hFt : ContinuousOn F0 t := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : t.domRestrict F0 = ⇑g := by
      funext y
      exact hFt_pt y
    rw [heq]
    exact g.continuous
  have hU : ContinuousOn F0 (s ∪ t) :=
    hFs.union_of_isClosed hFt hs ht
  rw [hcover] at hU
  have hcont : Continuous F0 := continuousOn_univ.mp hU
  refine ⟨⟨F0, hcont⟩, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro y
    change F0 (y : X) = f y
    exact hFs_pt y
  · apply ContinuousMap.ext
    intro y
    change F0 (y : X) = g y
    exact hFt_pt y

/-- Binary closed-cover gluing of `CommSq` lifts in `TopCat`.

Given a commutative square with a binary closed cover of the lift source,
and local lifts on each closed piece agreeing on the overlap and respecting
both triangles, there is a global lift. -/
theorem exists_lift_of_binary_closed_cover
    {A B X Y : TopCat.{u}} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CategoryTheory.CommSq f i p g)
    {s t : Set B}
    (hs : IsClosed s) (ht : IsClosed t)
    (hcover : s ∪ t = Set.univ)
    (ls : ContinuousMap s X) (lt : ContinuousMap t X)
    (hagree : ∀ (b : B) (hbs : b ∈ s) (hbt : b ∈ t),
      ls ⟨b, hbs⟩ = lt ⟨b, hbt⟩)
    (hleft_s : ∀ (a : A) (h : i a ∈ s), ls ⟨i a, h⟩ = f a)
    (hleft_t : ∀ (a : A) (h : i a ∈ t), lt ⟨i a, h⟩ = f a)
    (hright_s : ∀ (b : B) (h : b ∈ s), p (ls ⟨b, h⟩) = g b)
    (hright_t : ∀ (b : B) (h : b ∈ t), p (lt ⟨b, h⟩) = g b) :
    CategoryTheory.CommSq.HasLift sq := by
  obtain ⟨F, hFs, hFt⟩ :=
    exists_continuousMap_glue_of_closed_cover hs ht hcover ls lt hagree
  have hFs_pt : ∀ (b : B) (h : b ∈ s), F b = ls ⟨b, h⟩ := fun b h => by
    rw [← hFs, ContinuousMap.restrict_apply]
  have hFt_pt : ∀ (b : B) (h : b ∈ t), F b = lt ⟨b, h⟩ := fun b h => by
    rw [← hFt, ContinuousMap.restrict_apply]
  let l : B ⟶ X := TopCat.ofHom F
  have hl_app : ∀ (b : B), l b = F b := fun b => TopCat.ofHom_apply F b
  have hmem : ∀ (b : B), b ∈ s ∪ t := fun b => by
    rw [hcover]
    trivial
  have h_left : i ≫ l = f := by
    apply TopCat.ext
    intro a
    have hmem_a : i a ∈ s ∪ t := hmem (i a)
    rcases Set.mem_or_mem_of_mem_union hmem_a with h | h
    · rw [TopCat.comp_app, hl_app, hFs_pt _ h, hleft_s _ h]
    · rw [TopCat.comp_app, hl_app, hFt_pt _ h, hleft_t _ h]
  have h_right : l ≫ p = g := by
    apply TopCat.ext
    intro b
    have hmem_b : b ∈ s ∪ t := hmem b
    rcases Set.mem_or_mem_of_mem_union hmem_b with h | h
    · rw [TopCat.comp_app, hl_app, hFs_pt _ h, hright_s _ h]
    · rw [TopCat.comp_app, hl_app, hFt_pt _ h, hright_t _ h]
  exact CategoryTheory.CommSq.HasLift.mk' (sq := sq) ⟨l, h_left, h_right⟩

end TopCat
