/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/CapSet/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The dimension-three statement uses Mathlib's additive Roth number for the value tabulated at
commit e2e19eef093a77882da57f348def029533ec2d5e.
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases

/-!
# Largest cap set in dimension three

Slice a cap by its last coordinate. Each planar slice has at most four points. If the largest
two slices have at least four and three points, their sumset misses at most one planar point.
The negative of the third slice lies in this complement. Both planar bounds can be checked
in the nine-point affine plane. The graph of the quadratic form `x² + y²` attains the bound.
-/

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

open Finset
open scoped Pointwise

private abbrev Plane := ZMod 3 × ZMod 3
private abbrev Space := Fin 3 → ZMod 3

private def point (i : ZMod 3) (p : Plane) : Space := ![p.1, p.2, i]

private def slice (s : Finset Space) (i : ZMod 3) : Finset Plane :=
  univ.filter fun p => point i p ∈ s

private lemma mem_slice {s : Finset Space} {i : ZMod 3} {p : Plane} :
    p ∈ slice s i ↔ point i p ∈ s := by simp [slice]

private lemma sum_card_slice (s : Finset Space) : ∑ i, (slice s i).card = s.card := by
  have eta (x : Space) : point (x 2) (x 0, x 1) = x := by
    funext j
    fin_cases j <;> rfl
  rw [← card_sigma]
  refine card_nbij' (fun x => point x.1 x.2) (fun x => ⟨x 2, x 0, x 1⟩) ?_ ?_ ?_ ?_
  · exact fun _ hx => mem_slice.mp (mem_sigma.mp hx).2
  · exact fun x hx => mem_sigma.mpr ⟨mem_univ _, mem_slice.mpr ((eta x).symm ▸ hx)⟩
  · exact fun _ _ => rfl
  · exact fun x _ => eta x

private lemma point_add_eq {a b c : Plane} {i j k : ZMod 3}
    (hp : a + c = b + b) (hi : i + k = j + j) :
    point i a + point k c = point j b + point j b := by
  funext l
  fin_cases l
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp
  · exact hi

private lemma slice_free {s : Finset Space} (hs : ThreeAPFree (s : Set Space)) (i : ZMod 3) :
    ThreeAPFree (slice s i : Set Plane) := by
  intro a ha b hb c hc h
  have he := hs (mem_slice.mp ha) (mem_slice.mp hb) (mem_slice.mp hc) (point_add_eq h rfl)
  exact Prod.ext (congrFun he 0) (congrFun he 1)

section

-- Enumerate only subsets of the specified cardinalities.
attribute [local instance 2000] Finset.decidableDforallFinset

private lemma plane_bound : addRothNumber (univ : Finset Plane) ≤ 4 := by
  exact Nat.le_of_lt_succ (addRothNumber_lt_of_forall_not_threeAPFree (by decide +kernel))

private lemma plane_sumset {a b : Finset Plane}
    (ha : a.card = 4) (hfa : ThreeAPFree (a : Set Plane))
    (hb : b.card = 3) (hfb : ThreeAPFree (b : Set Plane)) :
    (univ \ (a + b)).card ≤ 1 := by
  -- A four-point set translates to one with sum zero, since four is one in the field.
  let centered := (powersetCard 4 (univ : Finset Plane)).filter fun s =>
    (∑ p ∈ s, p) = 0 ∧ ThreeAPFree (s : Set Plane)
  let triangles := (powersetCard 3 (univ : Finset Plane)).filter fun (t : Finset Plane) =>
    ThreeAPFree (t : Set Plane)
  have check : ∀ s ∈ centered, ∀ t ∈ triangles, (univ \ (s + t)).card ≤ 1 := by decide +kernel
  let c := -(∑ p ∈ a, p)
  have hcenter : ∑ p ∈ ({c} + a), p = 0 := by
    have he : {c} + a = a.image (c + ·) := image₂_singleton_left
    rw [he, sum_image (add_right_injective c).injOn, sum_add_distrib, sum_const, ha]
    exact (by decide : ∀ p : Plane, 4 • -p + p = 0) _
  have hfree : ThreeAPFree (({c} + a : Finset Plane) : Set Plane) := by
    rw [coe_add, coe_singleton, Set.singleton_add]
    exact hfa.vadd_set
  have h := check ({c} + a) (mem_filter.mpr
    ⟨mem_powersetCard.mpr ⟨subset_univ _, by simpa using ha⟩, hcenter, hfree⟩)
    b (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hb⟩, hfb⟩)
  simpa only [add_assoc, card_sdiff_of_subset (subset_univ _), card_singleton_add] using h

end

private lemma neg_slice_subset {s : Finset Space} (hs : ThreeAPFree (s : Set Space))
    {i j k : ZMod 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    -(slice s j) ⊆ univ \ (slice s i + slice s k) := by
  intro x hx
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro h
  obtain ⟨a, ha, c, hc, rfl⟩ := mem_add.mp h
  have hmid := mem_slice.mp (mem_neg'.mp hx)
  have hd : ∀ p : Plane, p = -p + -p := by decide
  have ht : ∀ i j k : ZMod 3, i ≠ j → j ≠ k → i ≠ k → i + k = j + j := by decide
  have he := hs (mem_slice.mp ha) hmid (mem_slice.mp hc)
    (point_add_eq (hd _) (ht i j k hij hjk hik))
  exact hij (congrFun he 2)

private lemma cap_card_le {s : Finset Space} (hs : ThreeAPFree (s : Set Space)) :
    s.card ≤ 9 := by
  let n : Fin 3 → ℕ := fun i => (slice s i).card
  let σ := Tuple.sort n
  have h01 : n (σ 0) ≤ n (σ 1) := Tuple.monotone_sort n (by decide : (0 : Fin 3) ≤ 1)
  have h12 : n (σ 1) ≤ n (σ 2) := Tuple.monotone_sort n (by decide : (1 : Fin 3) ≤ 2)
  have hsum : n (σ 0) + n (σ 1) + n (σ 2) = s.card := by
    rw [← Fin.sum_univ_three (fun i => n (σ i)), Equiv.sum_comp σ n]
    exact sum_card_slice s
  have hmax : n (σ 2) ≤ 4 :=
    ((slice_free hs _).le_addRothNumber (subset_univ _)).trans plane_bound
  by_contra! h
  have h₄ : n (σ 2) = 4 := by omega
  obtain ⟨b, hb, hbcard⟩ := exists_subset_card_eq (show 3 ≤ n (σ 1) by omega)
  have hbound := plane_sumset h₄ (slice_free hs _) hbcard ((slice_free hs _).mono hb)
  have hsub := neg_slice_subset hs (i := σ 2) (j := σ 0) (k := σ 1)
    (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
  have hsmall : n (σ 0) ≤ 1 := calc
    n (σ 0) = (-(slice s (σ 0))).card := (card_neg _).symm
    _ ≤ _ := card_le_card (hsub.trans (Finset.sdiff_subset_sdiff_right _ (add_subset_add_left hb)))
    _ ≤ 1 := hbound
  omega

/-- **Largest cap set in dimension three.** Let $\mathbb{F}_3$ be the field with three elements.
The largest subset of $\mathbb{F}_3^3$ containing no three-term arithmetic progression, that is,
no elements $a, b, c$ of the subset with $a + c = 2b$ and $a \neq b$, has exactly $9$ elements.

Over $\mathbb{F}_3$ these subsets are exactly the caps: sets with no three distinct collinear
points.

Source: exhaustive search; OEIS A090245; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/CapSet/README.md`. -/
public theorem capSet_dim_three :
    addRothNumber (Finset.univ : Finset (Fin 3 → ZMod 3)) = 9 := by
  apply le_antisymm
  · obtain ⟨s, _, hcard, hs⟩ := addRothNumber_spec (univ : Finset Space)
    exact hcard ▸ cap_card_le hs
  · let s := (univ : Finset Plane).image fun p => point (p.1 ^ 2 + p.2 ^ 2) p
    have hs : ThreeAPFree (s : Set Space) := by decide +kernel
    have hcard : s.card = 9 := by decide +kernel
    exact hcard ▸ hs.le_addRothNumber (subset_univ _)

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
