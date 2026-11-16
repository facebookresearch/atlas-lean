/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Fooling sets for communication complexity

A 1-fooling set for `f : X × Y → Bool` forces any cover of
the input space by monochromatic-1 rectangles to have at
least `|S|` rectangles: two fooling elements cannot share
a rectangle. This is the fooling-set lower bound; rank
bounds are not included here.
-/

@[expose] public section

/-- A rectangle in `X × Y`: a product of subsets. A partition
of the input space into monochromatic rectangles lower-bounds
communication (core of MOD-59). A set `S ⊆ X × Y` is a
1-fooling set for `f` when `f` is `1` on all of `S` and every
rectangle containing two distinct elements of `S` also
contains an input where `f` is `0`: formally, for distinct
`(x,y), (x',y') ∈ S`, `f (x, y') = 0 ∨ f (x', y) = 0`. -/
def IsFooling {X Y : Type*} (f : X × Y → Bool) (S : Finset (X × Y)) : Prop :=
  (∀ p ∈ S, f p = true) ∧
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    f (p.1, q.2) = false ∨ f (q.1, p.2) = false

/-- A rectangle (given by its two sides) is monochromatic-1
for `f` when `f` is `1` on the whole product. -/
def RectMono {X Y : Type*} (f : X × Y → Bool) (A : Finset X) (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, f (x, y) = true

/-- Fooling bound: if the whole space `univ ×ˢ univ` is
covered by `k` monochromatic-1 rectangles (as a list of side
pairs) and `S` is a fooling set, then `S.card ≤ k`. Two
fooling elements cannot share a rectangle. -/
theorem fooling_card_le {X Y : Type*} [Fintype X] [Fintype Y]
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
    by_contra hne
    have hvalne : a.val ≠ b.val := fun heq => hne (Subtype.ext heq)
    have hmem_a : a.val.1 ∈ (g a).1 ∧ a.val.2 ∈ (g a).2 := (hg a).2
    have hmem_b : b.val.1 ∈ (g b).1 ∧ b.val.2 ∈ (g b).2 := (hg b).2
    rw [← hgab] at hmem_b
    have hrlist : g a ∈ rects := List.mem_toFinset.mp (hg a).1
    have hmon : RectMono f (g a).1 (g a).2 := hmono _ hrlist
    have hcross1 : f (a.val.1, b.val.2) = true := hmon _ hmem_a.1 _ hmem_b.2
    have hcross2 : f (b.val.1, a.val.2) = true := hmon _ hmem_b.1 _ hmem_a.2
    have hfool := hS.2 a.val a.property b.val b.property hvalne
    rcases hfool with h0 | h0
    · rw [hcross1] at h0
      exact Bool.noConfusion h0
    · rw [hcross2] at h0
      exact Bool.noConfusion h0
  have hcard : Fintype.card ↥S ≤ Fintype.card ↥(rects.toFinset) :=
    Fintype.card_le_of_injective F hinj
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact le_trans hcard (List.toFinset_card_le rects)

end
