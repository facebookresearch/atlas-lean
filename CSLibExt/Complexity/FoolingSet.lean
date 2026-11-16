/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Fooling sets and rectangle covers

A 1-fooling set for a Boolean function `f : X × Y → Bool` is a finite set `S` of inputs on
which `f` is `true` such that, for any two distinct elements `(x, y)` and `(x', y')` of `S`,
one of the crossed inputs `(x, y')` and `(x', y)` has value `false`. A rectangle `A ×ˢ B`
on which `f` is constantly `true` therefore contains at most one element of `S`, so any
list of such rectangles covering `S` has at least `S.card` entries.

In communication complexity this counting step is the core of the fooling-set lower bound.
Protocols and their cost are not modeled here, and rank bounds are not included.

## Main results

* `Cslib.Complexity.FoolingSet.IsFooling`: `S` is a 1-fooling set for `f`.
* `Cslib.Complexity.FoolingSet.RectMono`: `f` is `true` on the rectangle `A ×ˢ B`.
* `Cslib.Complexity.FoolingSet.IsFooling.eq_of_mem_rect`: a monochromatic-1 rectangle
  contains at most one element of a 1-fooling set.
* `Cslib.Complexity.FoolingSet.fooling_card_le`: a list of monochromatic-1 rectangles
  covering a 1-fooling set `S` has length at least `S.card`.

## References

* E. Kushilevitz and N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997, Chapter 1.
-/

@[expose] public section

namespace Cslib.Complexity.FoolingSet

/-- `S` is a 1-fooling set for `f`: `f` is `true` on every element of `S`, and for distinct
`p, q ∈ S` one of the crossed inputs `(p.1, q.2)` and `(q.1, p.2)` has value `false`. -/
def IsFooling {X Y : Type*} (f : X × Y → Bool) (S : Finset (X × Y)) : Prop :=
  (∀ p ∈ S, f p = true) ∧
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    f (p.1, q.2) = false ∨ f (q.1, p.2) = false

/-- The rectangle `A ×ˢ B`, given by its two sides, is monochromatic-1 for `f`: `f` is
`true` on all of it. -/
def RectMono {X Y : Type*} (f : X × Y → Bool) (A : Finset X) (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, f (x, y) = true

/-- A monochromatic-1 rectangle contains at most one element of a 1-fooling set: for
distinct `p, q ∈ S` in `A ×ˢ B`, the crossed inputs would also lie in `A ×ˢ B`, where `f` is
`true`. -/
theorem IsFooling.eq_of_mem_rect {X Y : Type*} {f : X × Y → Bool} {S : Finset (X × Y)}
    (hS : IsFooling f S) {A : Finset X} {B : Finset Y} (hAB : RectMono f A B)
    {p q : X × Y} (hp : p ∈ S) (hq : q ∈ S) (hpA : p.1 ∈ A) (hpB : p.2 ∈ B)
    (hqA : q.1 ∈ A) (hqB : q.2 ∈ B) : p = q := by
  by_contra hne
  rcases hS.2 p hp q hq hne with h | h
  · rw [hAB _ hpA _ hqB] at h
    exact Bool.noConfusion h
  · rw [hAB _ hqA _ hpB] at h
    exact Bool.noConfusion h

/-- Fooling-set bound: if every element of a 1-fooling set `S` lies in one of the
monochromatic-1 rectangles listed in `rects` (for example, when the rectangles cover every
input on which `f` is `true`), then `S.card ≤ rects.length`. Two distinct elements of `S`
never share a rectangle. -/
theorem fooling_card_le {X Y : Type*}
    (f : X × Y → Bool) (S : Finset (X × Y)) (hS : IsFooling f S)
    (rects : List (Finset X × Finset Y))
    (hmono : ∀ r ∈ rects, RectMono f r.1 r.2)
    (hcover : ∀ p ∈ S, ∃ r ∈ rects, p.1 ∈ r.1 ∧ p.2 ∈ r.2) :
    S.card ≤ rects.length := by
  classical
  have hcover' : ∀ p ∈ S, ∃ r ∈ rects.toFinset, p.1 ∈ r.1 ∧ p.2 ∈ r.2 := by
    intro p hp
    obtain ⟨r, hrlist, hpx, hpy⟩ := hcover p hp
    exact ⟨r, List.mem_toFinset.mpr hrlist, hpx, hpy⟩
  have hchoice : ∀ s : ↥S, ∃ r ∈ rects.toFinset, s.val.1 ∈ r.1 ∧ s.val.2 ∈ r.2 :=
    fun s => hcover' s.val s.property
  choose g hg using hchoice
  let F : ↥S → ↥(rects.toFinset) := fun s => ⟨g s, (hg s).1⟩
  have hinj : Function.Injective F := by
    intro a b hab
    have hgab : g a = g b := congrArg Subtype.val hab
    have hmem_a : a.val.1 ∈ (g a).1 ∧ a.val.2 ∈ (g a).2 := (hg a).2
    have hmem_b : b.val.1 ∈ (g a).1 ∧ b.val.2 ∈ (g a).2 := by
      rw [hgab]
      exact (hg b).2
    have hmon : RectMono f (g a).1 (g a).2 := hmono _ (List.mem_toFinset.mp (hg a).1)
    exact Subtype.ext (hS.eq_of_mem_rect hmon a.property b.property hmem_a.1 hmem_a.2
      hmem_b.1 hmem_b.2)
  have hcard : Fintype.card ↥S ≤ Fintype.card ↥(rects.toFinset) :=
    Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact le_trans hcard (List.toFinset_card_le rects)

end Cslib.Complexity.FoolingSet
