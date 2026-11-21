/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.RepresentationTheory.GroupCohomology.CyclicCarry

open CategoryTheory groupCohomology

/-- Exact-source consumer, with the original binders: the carry cochain
unfolds to its defining case split. -/
example {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) {A : Rep ℤ G} (a : A) (p : G × G) :
    carryFun s hs hfin a p =
      if orderOf s ≤ cyclicLog s hs hfin p.1 + cyclicLog s hs hfin p.2
        then a else 0 :=
  rfl

universe u

/-- The carry API is available in every universe. -/
example {G : Type u} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) (g : G) : s ^ cyclicLog s hs hfin g = g :=
  pow_cyclicLog s hs hfin g

private theorem hord3 :
    orderOf (Multiplicative.ofAdd (1 : ZMod 3)) = 3 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private theorem hs3 :
    ∀ g : Multiplicative (ZMod 3),
      g ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 3)) := by
  intro g
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨((Multiplicative.toAdd g).val : ℤ), ?_⟩
  rw [zpow_natCast, ← ofAdd_nsmul]
  simp

private theorem hfin3 :
    IsOfFinOrder (Multiplicative.ofAdd (1 : ZMod 3)) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨3, by norm_num, ?_⟩
  have h := pow_orderOf_eq_one (Multiplicative.ofAdd (1 : ZMod 3))
  rwa [hord3] at h

/-- Nontrivial instance: in the cyclic group of order three, the carry
vanishes on `(s, s)` but takes the value `a` on `(s ^ 2, s ^ 2)`. -/
example {A : Rep ℤ (Multiplicative (ZMod 3))} (a : A) :
    carryFun (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3 a
        (Multiplicative.ofAdd (1 : ZMod 3),
          Multiplicative.ofAdd (1 : ZMod 3)) = 0 ∧
      carryFun (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3 a
        ((Multiplicative.ofAdd (1 : ZMod 3)) ^ 2,
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ 2) = a := by
  have h1 : cyclicLog (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3
      (Multiplicative.ofAdd (1 : ZMod 3)) = 1 :=
    cyclicLog_eq_of_pow_eq_of_lt _ _ (pow_one _) (by rw [hord3]; norm_num)
  have h2 : cyclicLog (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3
      ((Multiplicative.ofAdd (1 : ZMod 3)) ^ 2) = 2 :=
    cyclicLog_eq_of_pow_eq_of_lt _ _ rfl (by rw [hord3]; norm_num)
  constructor
  · apply carryFun_of_lt
    rw [h1, hord3]
    norm_num
  · apply carryFun_of_le
    rw [h2, hord3]
    norm_num

/-- The cyclic invariant of a constant function is the order multiple. -/
example {G : Type} [Group G] (s : G) {A : Rep ℤ G} (a : A) :
    cyclicInv s (fun _ => a) = orderOf s • a := by
  rw [cyclicInv_apply, Finset.sum_const, Finset.card_range]
