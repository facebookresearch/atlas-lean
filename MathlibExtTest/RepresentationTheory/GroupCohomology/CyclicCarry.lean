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

private theorem hlog3_one :
    cyclicLog (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3
      (Multiplicative.ofAdd (1 : ZMod 3)) = 1 :=
  cyclicLog_eq_of_pow_eq_of_lt _ _ (pow_one _) (by rw [hord3]; norm_num)

private theorem hlog3_two :
    cyclicLog (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3
      ((Multiplicative.ofAdd (1 : ZMod 3)) ^ 2) = 2 :=
  cyclicLog_eq_of_pow_eq_of_lt _ _ rfl (by rw [hord3]; norm_num)

/-- Off-diagonal pairs at the threshold: in the cyclic group of order three the
logarithms of `s` and `s ^ 2` add up to the order `3`, so the carry takes the
value `a` on both `(s, s ^ 2)` and `(s ^ 2, s)`. Unlike the diagonal pairs above,
these detect a strict threshold and a carry that reads one entry twice. -/
example {A : Rep ℤ (Multiplicative (ZMod 3))} (a : A) :
    carryFun (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3 a
        (Multiplicative.ofAdd (1 : ZMod 3),
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ 2) = a ∧
      carryFun (Multiplicative.ofAdd (1 : ZMod 3)) hs3 hfin3 a
        ((Multiplicative.ofAdd (1 : ZMod 3)) ^ 2,
          Multiplicative.ofAdd (1 : ZMod 3)) = a := by
  constructor
  · apply carryFun_of_le
    rw [hlog3_one, hlog3_two, hord3]
  · apply carryFun_of_le
    rw [hlog3_one, hlog3_two, hord3]

/-- The cyclic sum of a constant function is the order multiple. -/
example {G : Type} [Group G] (s : G) {A : Rep ℤ G} (a : A) :
    cyclicInv s (fun _ => a) = orderOf s • a := by
  rw [cyclicInv_apply, Finset.sum_const, Finset.card_range]

private def asymPair (p : Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :
    Rep.trivial ℤ (Multiplicative (ZMod 3)) ℤ :=
  if p = ((Multiplicative.ofAdd (1 : ZMod 3)) ^ 2, Multiplicative.ofAdd (1 : ZMod 3))
    then (1 : ℤ) else 0

/-- Asymmetric fixture on the cyclic group of order three: the function with value
`1` at `(s ^ 2, s)` and `0` elsewhere (in the trivial representation on `ℤ`) has
cyclic sum `1`, while the same sum with the two inputs reversed is `0`, so the test
detects the order of the inputs, which the constant function above cannot. -/
example :
    cyclicInv (Multiplicative.ofAdd (1 : ZMod 3)) asymPair = (1 : ℤ) ∧
      ∑ i ∈ Finset.range (orderOf (Multiplicative.ofAdd (1 : ZMod 3))),
        asymPair (Multiplicative.ofAdd (1 : ZMod 3),
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ i) = (0 : ℤ) := by
  rw [cyclicInv_apply, hord3]
  decide

private theorem horderInt : orderOf (Multiplicative.ofAdd (1 : ℤ)) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_one, Nat.cast_eq_zero] at h
  omega

/-- Outside the finite case the sum is empty: the generator of the infinite cyclic
group has `orderOf s = 0`, so the cyclic sum of every function is `0`. -/
example {A : Rep ℤ (Multiplicative ℤ)} (c : Multiplicative ℤ × Multiplicative ℤ → A) :
    cyclicInv (Multiplicative.ofAdd (1 : ℤ)) c = 0 := by
  rw [cyclicInv_apply, horderInt, Finset.sum_range_zero]
