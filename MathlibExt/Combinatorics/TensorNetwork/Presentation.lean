/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: ported the source conversions between complete-graph tensors and
factored tensor networks, with explicit finite label alphabets in place of finite carriers.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Basic

/-! # Equivalent presentations of finite tensor networks

This module converts between `TensorNetwork.Instance` and `TensorNetwork.Factored` without
changing their values. The source used an ambient finite label type; the Atlas version takes an
explicit finite alphabet and keeps the carrier unrestricted.

Adapted from `eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {J σ τ A : Type*}

/-- A product over directed pairs of distinct vertices, regrouped by unordered pairs. -/
private theorem prod_erase_eq_orderedPairs [Fintype J] [LinearOrder J]
    (G : J → J → ℤ) :
    ∏ a, ∏ b ∈ univ.erase a, G a b =
      ∏ p ∈ orderedPairs J, G p.1 p.2 * G p.2 p.1 := by
  rw [← Finset.prod_finset_product' (univ.filter fun p : J × J => p.1 ≠ p.2)
    univ (fun a => univ.erase a) (by intro p; simp [eq_comm])]
  rw [Finset.prod_mul_distrib]
  have hreverse :
      ∏ p ∈ orderedPairs J, G p.2 p.1 =
        ∏ p ∈ univ.filter (fun p : J × J => p.2 < p.1), G p.1 p.2 :=
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp)
      (by intro p; simp) (by intro p; simp) (by intro p; simp) (by intro p; simp)
  rw [hreverse, orderedPairs, ← Finset.prod_union]
  · congr 1
    ext p
    simp [lt_or_lt_iff_ne]
  · rw [Finset.disjoint_left]
    intro p
    simp
    grind

/-- Rename the active part of a finite alphabet through a bijection, with zero off it. -/
private theorem sum_renamed [DecidableEq A] (labels D : Finset A) (dec : A → τ) (Θ : Finset τ)
    (hD : D ⊆ labels) (hdec : Set.BijOn dec D Θ) (f g : τ → ℤ) :
    ∑ x ∈ labels, (if x ∈ D then f (dec x) else 0) *
      (if x ∈ D then g (dec x) else 0) = ∑ θ ∈ Θ, f θ * g θ := by
  calc
    _ = ∑ x ∈ D, (if x ∈ D then f (dec x) else 0) *
        (if x ∈ D then g (dec x) else 0) :=
      (Finset.sum_subset hD (by intro x _ hx; simp [hx])).symm
    _ = ∑ x ∈ D, f (dec x) * g (dec x) := by
      exact Finset.sum_congr rfl fun x hx => by simp [hx]
    _ = ∑ θ ∈ Θ, f θ * g θ :=
      Finset.sum_nbij dec (fun x hx => hdec.mapsTo hx) hdec.injOn hdec.surjOn
        (fun _ _ => rfl)

namespace Factored

/-- Turn a factored network into a complete-graph tensor instance.

The finite set `D a b` names the source labels on the edge `{a, b}` through `dec a b`.
Labels outside `D a b` make the corresponding directed factor zero. -/
def toInstance [Fintype J] [LinearOrder J] [DecidableEq A] (N : Factored J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) : Instance J A :=
  fun a θ => ∑ z ∈ N.S a, N.W a z *
    ∏ b ∈ univ.erase a,
      if θ b ∈ D (min a b) (max a b) then
        N.f a b z (dec (min a b) (max a b) (θ b))
      else 0

/-- Naming every source edge alphabet bijectively inside `labels` preserves network value. -/
theorem value_toInstance [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Factored J σ τ) (labels : Finset A) (default : A)
    (D : J → J → Finset A) (dec : J → J → A → τ)
    (hD : ∀ a b, a < b → D a b ⊆ labels)
    (hdec : ∀ a b, a < b → Set.BijOn (dec a b) (D a b) (N.Θ a b)) :
    (N.toInstance D dec).value labels default = N.value := by
  unfold Instance.value Factored.value toInstance
  simp only [Finset.prod_univ_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Finset.prod_mul_distrib, ← Finset.mul_sum]
  congr 1
  have key : ∀ labeling : J × J → A,
      ∏ a, ∏ b ∈ univ.erase a,
        (if incidentLabels labeling a b ∈ D (min a b) (max a b) then
          N.f a b (z a)
            (dec (min a b) (max a b) (incidentLabels labeling a b)) else 0) =
      ∏ p : J × J with p.1 < p.2,
        (if labeling p ∈ D p.1 p.2 then
          N.f p.1 p.2 (z p.1) (dec p.1 p.2 (labeling p)) else 0) *
        (if labeling p ∈ D p.1 p.2 then
          N.f p.2 p.1 (z p.2) (dec p.1 p.2 (labeling p)) else 0) := by
    intro labeling
    rw [prod_erase_eq_orderedPairs]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.1 < p.2 := by simpa using hp
    simp [incidentLabels, pairIndex, hp'.le]
  simp only [key]
  rw [edgeLabelings]
  let H : J × J → A → ℤ := fun p x =>
    (if x ∈ D p.1 p.2 then
      N.f p.1 p.2 (z p.1) (dec p.1 p.2 x) else 0) *
    (if x ∈ D p.1 p.2 then
      N.f p.2 p.1 (z p.2) (dec p.1 p.2 x) else 0)
  change (∑ x ∈ Fintype.piFinsetOn (fun p : J × J => p.1 < p.2)
      (fun _ => labels) default, ∏ p with p.1 < p.2, H p (x p)) = _
  rw [Fintype.sum_piFinsetOn_prod
    (fun p : J × J => p.1 < p.2) (fun _ => labels) default H]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa using hp
  dsimp only [H]
  rw [sum_renamed labels (D p.1 p.2) (dec p.1 p.2) (N.Θ p.1 p.2)
    (hD p.1 p.2 hp') (hdec p.1 p.2 hp')]
  simp [Factored.interaction, Factored.labelSet, hp'.le]

end Factored

namespace Instance

/-- Present an instance as a half-edge network.

A state at `v` chooses one label for every off-diagonal half-edge from `v`; the two sides of
each edge are constrained to agree. The capacities are zero because this construction makes no
size claim. -/
def toFactored [Fintype J] [DecidableEq J] [DecidableEq A]
    (R : Instance J A) (labels : Finset A) (default : A) :
    Factored J (J → A) A where
  S v := Fintype.piFinsetOn (fun w => w ≠ v) (fun _ => labels) default
  W := R
  Θ _ _ := labels
  f _ w z θ := if z w = θ then 1 else 0
  c _ _ := 0

/-- The half-edge presentation of an instance has the same value. -/
theorem value_toFactored [Fintype J] [LinearOrder J] [DecidableEq A]
    (R : Instance J A) (labels : Finset A) (default : A) :
    R.value labels default = (R.toFactored labels default).value := by
  rw [← Factored.value_toInstance (R.toFactored labels default) labels default
    (fun _ _ => labels) (fun _ _ => id) (by simp)
    (by intro a b hab; simpa [toFactored] using Set.bijOn_id (labels : Set A))]
  unfold Instance.value
  refine Finset.sum_congr rfl fun labeling hlabeling => ?_
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold Factored.toInstance toFactored
  symm
  rw [Finset.sum_eq_single (incidentLabels labeling v)]
  · rw [Finset.prod_eq_one, mul_one]
    intro b hb
    have hbv : b ≠ v := by simpa using hb
    have hpair : (pairIndex v b).1 < (pairIndex v b).2 := by
      simpa [pairIndex] using (min_lt_max.mpr hbv.symm)
    have hallowed : incidentLabels labeling v b ∈ labels :=
      ((mem_edgeLabelings labels default labeling).mp hlabeling
        (pairIndex v b)).1 hpair
    simp [hallowed]
  · intro z hz hne
    have hz' := (Fintype.mem_piFinsetOn
      (fun w : J => w ≠ v) (fun _ => labels) default z).mp hz
    have hdiag : incidentLabels labeling v v = default := by
      exact ((mem_edgeLabelings labels default labeling).mp hlabeling
        (pairIndex v v)).2 (by simp [pairIndex])
    obtain ⟨b, hb⟩ : ∃ b, z b ≠ incidentLabels labeling v b := by
      by_contra hcon
      exact hne (funext fun b => by_contra fun hb => hcon ⟨b, hb⟩)
    have hbv : b ≠ v := by
      rintro rfl
      exact hb (by simpa [hdiag] using (hz' b).2 (by simp))
    have hpair : (pairIndex v b).1 < (pairIndex v b).2 := by
      simpa [pairIndex] using (min_lt_max.mpr hbv.symm)
    have hallowed : incidentLabels labeling v b ∈ labels :=
      ((mem_edgeLabelings labels default labeling).mp hlabeling
        (pairIndex v b)).1 hpair
    rw [Finset.prod_eq_zero (i := b) (by simp [hbv]), mul_zero]
    simp [hallowed, hb]
  · intro hn
    exfalso
    apply hn
    rw [Fintype.mem_piFinsetOn]
    intro w
    constructor
    · intro hwv
      have hpair : (pairIndex v w).1 < (pairIndex v w).2 := by
        simpa [pairIndex] using (min_lt_max.mpr hwv.symm)
      exact ((mem_edgeLabelings labels default labeling).mp hlabeling
        (pairIndex v w)).1 hpair
    · intro hwv
      have hw : w = v := not_ne_iff.mp hwv
      subst w
      exact ((mem_edgeLabelings labels default labeling).mp hlabeling
        (pairIndex v v)).2 (by simp [pairIndex])

/-- Expand an instance value as a sum over directed half-edge vectors with equality factors. -/
theorem value_eq_halfEdges [Fintype J] [LinearOrder J] [DecidableEq A]
    (R : Instance J A) (labels : Finset A) (default : A) :
    R.value labels default =
      ∑ ℓ ∈ Fintype.piFinset fun w : J =>
        Fintype.piFinsetOn (fun w' => w' ≠ w) (fun _ => labels) default,
        (∏ w, R w (ℓ w)) * ∏ p ∈ orderedPairs J,
          if ℓ p.1 p.2 = ℓ p.2 p.1 then 1 else 0 := by
  rw [Instance.value_toFactored]
  unfold Factored.value
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.1 < p.2 := by simpa using hp
  have hℓ' := (Fintype.mem_piFinset.mp hℓ)
  have hright : ℓ p.2 p.1 ∈ labels := by
    exact ((Fintype.mem_piFinsetOn
      (fun w : J => w ≠ p.2) (fun _ => labels) default (ℓ p.2)).mp (hℓ' p.2)
        p.1).1 hp'.ne
  simp [Factored.interaction, Factored.labelSet, toFactored, hp'.le, hright]

end Instance

end TensorNetwork
