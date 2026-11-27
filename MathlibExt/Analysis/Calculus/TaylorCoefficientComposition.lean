/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Cast.Field

/-!
# Faà di Bruno's formula for Taylor coefficients

This module proves Faà di Bruno's formula for the Taylor coefficients of a
composition of real functions, as a sum over integer partitions, by grouping
the ordered-partition form of the formula in Mathlib according to the
underlying integer partition.

The inner product space import supplies the `NormedSpace ℝ ℝ` instance inferred in the original
wanted statement via `RCLike.toInnerProductSpaceReal`.
-/

@[expose] public section

namespace MetaMathlibExt

namespace taylorCoeff_comp_eq_sum_partitions

open Finset Multiset OrderedFinpartition

/-- The integer partition underlying an ordered finpartition, given by the
multiset of its block sizes. -/
private def toPartition {n : ℕ} (c : OrderedFinpartition n) : Nat.Partition n where
  parts := (Finset.univ : Finset (Fin c.length)).val.map c.partSize
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hj⟩ := hi
    rw [← hj]
    exact c.partSize_pos j
  parts_sum := by
    change ∑ m, c.partSize m = n
    have hcard : (∑ m, c.partSize m)
        = Fintype.card (Σ m : Fin c.length, Fin (c.partSize m)) := by
      simp [Fintype.card_sigma]
    rw [hcard, Fintype.card_congr c.equivSigma]
    simp

@[simp]
private theorem toPartition_parts {n : ℕ} (c : OrderedFinpartition n) :
    (toPartition c).parts = (Finset.univ : Finset (Fin c.length)).val.map c.partSize :=
  rfl

private theorem toPartition_card {n : ℕ} (c : OrderedFinpartition n) :
    (toPartition c).parts.card = c.length := by
  simp [toPartition]

private theorem toPartition_count {n : ℕ} (c : OrderedFinpartition n) (i : ℕ) :
    (toPartition c).parts.count i
      = (Finset.univ.filter (fun j => c.partSize j = i)).card := by
  simp [toPartition]

/-- The product over the blocks of an ordered finpartition depends only on the
underlying integer partition. -/
private theorem prod_partSize_eq {n : ℕ} (c : OrderedFinpartition n) {R : Type*}
    [CommMonoid R] (B : ℕ → R) :
    ∏ j, B (c.partSize j)
      = ∏ i ∈ Finset.Icc 1 n, B i ^ (toPartition c).parts.count i := by
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin c.length)),
      c.partSize j ∈ Finset.Icc 1 n := fun j _ => by
    rw [Finset.mem_Icc]
    exact ⟨c.partSize_pos j, c.partSize_le j⟩
  rw [← Finset.prod_fiberwise_of_maps_to' hmaps B]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [toPartition_count, Finset.prod_const]

/-- The factorial-of-counts factor in `Multiset.bell_mul_eq` grows by
`m.count a + 1` when an occurrence of `a` is added. -/
private theorem prodCount_cons {m : Multiset ℕ} {a : ℕ} (ha : a ≠ 0) :
    ∏ j ∈ (a ::ₘ m).toFinset.erase 0, ((a ::ₘ m).count j).factorial
      = (m.count a + 1) * ∏ j ∈ m.toFinset.erase 0, (m.count j).factorial := by
  have hto : (a ::ₘ m).toFinset.erase 0 = insert a (m.toFinset.erase 0) := by
    ext j
    simp only [Finset.mem_erase, Multiset.mem_toFinset, Multiset.mem_cons,
      Finset.mem_insert, ne_eq]
    constructor
    · rintro ⟨hj0, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hj0, h⟩
    · rintro (rfl | ⟨hj0, h⟩)
      · exact ⟨ha, Or.inl rfl⟩
      · exact ⟨hj0, Or.inr h⟩
  rw [hto]
  have hne : ∀ j ∈ (m.toFinset.erase 0).erase a, (a ::ₘ m).count j = m.count j :=
    fun j hj => Multiset.count_cons_of_ne (Finset.mem_erase.mp hj).1 m
  by_cases hmem : a ∈ m.toFinset.erase 0
  · rw [Finset.insert_eq_of_mem hmem, ← Finset.mul_prod_erase _ _ hmem]
    conv_rhs => rw [← Finset.mul_prod_erase _ _ hmem]
    have hprod : ∏ j ∈ (m.toFinset.erase 0).erase a, ((a ::ₘ m).count j).factorial
        = ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j).factorial :=
      Finset.prod_congr rfl fun j hj => congrArg Nat.factorial (hne j hj)
    rw [hprod, Multiset.count_cons_self, Nat.factorial_succ]
    ring
  · rw [Finset.prod_insert hmem, Finset.prod_congr rfl
      (fun j hj => congrArg Nat.factorial
        (Multiset.count_cons_of_ne (fun h => by subst h; exact hmem hj) m) :
        ∀ j ∈ m.toFinset.erase 0, ((a ::ₘ m).count j).factorial
          = (m.count j).factorial),
      Multiset.count_cons_self]
    have h0 : m.count a = 0 := by
      by_contra hne
      exact hmem (by
        simp only [Finset.mem_erase, Multiset.mem_toFinset, ne_eq, ha, not_false_eq_true,
          true_and]
        exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
    rw [h0]
    simp

/-- Adding one occurrence of a positive part `a` to a multiset: the analogue
of the private Mathlib lemma `Multiset.bell_cons_mul_count`, proved here from
`Multiset.bell_mul_eq`. -/
private theorem bell_cons_mul_count' (m : Multiset ℕ) {a : ℕ} (ha : a ≠ 0) :
    (a ::ₘ m).bell * (a ::ₘ m).count a = (m.sum + a).choose a * m.bell := by
  have hD : ((a ::ₘ m).map fun j => j.factorial).prod
        * ∏ j ∈ (a ::ₘ m).toFinset.erase 0, ((a ::ₘ m).count j).factorial
      = a.factorial * (m.count a + 1) *
          ((m.map fun j => j.factorial).prod
            * ∏ j ∈ m.toFinset.erase 0, (m.count j).factorial) := by
    rw [Multiset.map_cons, Multiset.prod_cons, prodCount_cons ha]
    ring
  have hDpos : (0 : ℚ) < ((m.map fun j => j.factorial).prod
      * ∏ j ∈ m.toFinset.erase 0, (m.count j).factorial : ℕ) := by
    have h1 : 0 < (m.map fun j => j.factorial).prod := by
      simp [Nat.factorial_pos]
    have h2 : 0 < ∏ j ∈ m.toFinset.erase 0, (m.count j).factorial :=
      Finset.prod_pos fun j _ => Nat.factorial_pos _
    exact_mod_cast Nat.mul_pos h1 h2
  have hbell : ∀ x : Multiset ℕ, (x.bell : ℚ) = x.sum.factorial
      / (((x.map fun j => j.factorial).prod
        * ∏ j ∈ x.toFinset.erase 0, (x.count j).factorial) : ℕ) := by
    intro x
    have hdvd : (x.map fun j => j.factorial).prod
        * ∏ j ∈ x.toFinset.erase 0, (x.count j).factorial ∣ x.sum.factorial :=
      ⟨x.bell, by rw [← Multiset.bell_mul_eq x]; ring⟩
    rw [Multiset.bell_eq, Nat.cast_div_charZero hdvd]
  have hchoose : ((m.sum + a).choose a : ℚ) * (m.sum.factorial : ℕ) * (a.factorial : ℕ)
      = ((m.sum + a).factorial : ℕ) := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial m.sum a)
  have hne1 : ((((a ::ₘ m).map fun j => j.factorial).prod
      * ∏ j ∈ (a ::ₘ m).toFinset.erase 0, ((a ::ₘ m).count j).factorial : ℕ) : ℚ) ≠ 0 := by
    rw [hD]
    have h1 : 0 < (m.map fun j => j.factorial).prod := by simp [Nat.factorial_pos]
    have h2 : 0 < ∏ j ∈ m.toFinset.erase 0, (m.count j).factorial :=
      Finset.prod_pos fun j _ => Nat.factorial_pos _
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.succ_pos _))
      (Nat.mul_pos h1 h2)).ne'
  have hQ : ((a ::ₘ m).bell : ℚ) * ((a ::ₘ m).count a : ℚ)
      = ((m.sum + a).choose a : ℚ) * (m.bell : ℚ) := by
    rw [Multiset.count_cons_self, hbell, hbell, Multiset.sum_cons, div_mul_eq_mul_div]
    conv_rhs => rw [← mul_div_assoc]
    rw [div_eq_div_iff hne1 hDpos.ne', hD]
    push_cast
    have hfact : ((a + m.sum).factorial : ℚ)
        = ((m.sum + a).choose a : ℚ) * (m.sum.factorial : ℕ) * (a.factorial : ℕ) := by
      rw [add_comm a m.sum]
      exact hchoose.symm
    rw [hfact]
    ring
  exact_mod_cast hQ

/-- Extending on the left adds a singleton part. -/
private theorem toPartition_extendLeft_parts {n : ℕ} (c : OrderedFinpartition n) :
    (toPartition (c.extendLeft)).parts = 1 ::ₘ (toPartition c).parts := by
  apply Multiset.ext.mpr
  intro i
  have hcount : (toPartition c).parts.count i
      = (Finset.univ.filter (fun j : Fin c.length => c.partSize j = i)).card :=
    toPartition_count c i
  have hcountL : (toPartition (c.extendLeft)).parts.count i
      = (Finset.univ.filter
          (fun j : Fin (c.extendLeft.length) => c.extendLeft.partSize j = i)).card :=
    toPartition_count (c.extendLeft) i
  rw [hcountL, Multiset.count_cons, hcount, Finset.card_filter]
  have hsum : (∑ j : Fin c.extendLeft.length,
      (if c.extendLeft.partSize j = i then (1 : ℕ) else 0))
      = (if (1 : ℕ) = i then 1 else 0)
        + ∑ j : Fin c.length, (if c.partSize j = i then (1 : ℕ) else 0) := by
    have h := Fin.sum_univ_succ
      (f := fun j : Fin c.extendLeft.length =>
        if c.extendLeft.partSize j = i then (1 : ℕ) else 0) (n := c.length)
    simp only [OrderedFinpartition.extendLeft_partSize, Fin.cons_zero, Fin.cons_succ] at h
    exact h
  rw [hsum, ← Finset.card_filter]
  by_cases hi : i = 1
  · subst hi
    simp only [ite_true]
    ring
  · have h1 : (1 : ℕ) ≠ i := fun h => hi h.symm
    simp only [hi, h1, ite_false]
    ring

/-- Extending in the middle grows one part by one. -/
private theorem toPartition_extendMiddle_parts {n : ℕ} (c : OrderedFinpartition n)
    (j : Fin c.length) :
    (toPartition (c.extendMiddle j)).parts
      = (c.partSize j + 1) ::ₘ (toPartition c).parts.erase (c.partSize j) := by
  apply Multiset.ext.mpr
  intro i
  have hcount : (toPartition c).parts.count i
      = (Finset.univ.filter (fun k : Fin c.length => c.partSize k = i)).card :=
    toPartition_count c i
  have hcountM := toPartition_count (c.extendMiddle j) i
  have hpart : ∀ k : Fin c.length,
      (c.extendMiddle j).partSize k
        = Function.update c.partSize j (c.partSize j + 1) k := by
    intro k
    rw [OrderedFinpartition.extendMiddle_partSize]
  have hfilter : (Finset.univ.filter
      (fun k : Fin c.length => Function.update c.partSize j (c.partSize j + 1) k = i))
      = if i = c.partSize j + 1 then
          insert j (Finset.univ.filter (fun k : Fin c.length => c.partSize k = i))
        else (Finset.univ.filter
          (fun k : Fin c.length => c.partSize k = i)).erase j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hkj : k = j
    · rw [hkj]
      simp only [Function.update_self]
      split_ifs with hi
      · simp [hi]
      · have hne : c.partSize j + 1 ≠ i := fun h => hi h.symm
        simp [hne]
    · have hupd : Function.update c.partSize j (c.partSize j + 1) k
          = c.partSize k := Function.update_of_ne hkj _ _
      rw [hupd]
      split_ifs with hi
      · simp [hkj]
      · simp [hkj]
  have hsumEq : (∑ x : Fin (c.extendMiddle j).length,
      (if (c.extendMiddle j).partSize x = i then (1 : ℕ) else 0))
      = (Finset.univ.filter
          (fun k => Function.update c.partSize j (c.partSize j + 1) k = i)).card := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => by rw [hpart x]
  rw [hcountM, Finset.card_filter, hsumEq, hfilter]
  by_cases hi : i = c.partSize j + 1
  · rw [ite_eq_left hi]
    have hjnot : j ∉ Finset.univ.filter
        (fun k : Fin c.length => c.partSize k = i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
      exact (Nat.lt_succ_self _).ne
    rw [Finset.card_insert_of_notMem hjnot, Multiset.count_cons]
    have herase : ((toPartition c).parts.erase (c.partSize j)).count i
        = (toPartition c).parts.count i :=
      Multiset.count_erase_of_ne (by rw [hi]; exact Nat.succ_ne_self _) _
    rw [herase, hcount]
    simp [hi]
  · rw [ite_eq_right hi, Multiset.count_cons]
    have hcardE : ((Finset.univ.filter
          (fun k : Fin c.length => c.partSize k = i)).erase j).card
        = (Finset.univ.filter (fun k : Fin c.length => c.partSize k = i)).card
          - (if c.partSize j = i then 1 else 0) := by
      by_cases hjmem : j ∈ Finset.univ.filter
          (fun k : Fin c.length => c.partSize k = i)
      · rw [Finset.card_erase_of_mem hjmem]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
        rw [ite_eq_left hjmem]
      · rw [Finset.erase_eq_of_notMem hjmem]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
        rw [ite_eq_right hjmem]
        simp
    rw [hcardE]
    by_cases hfi : c.partSize j = i
    · rw [ite_eq_left hfi]
      have herase : ((toPartition c).parts.erase (c.partSize j)).count i
          = (toPartition c).parts.count i - 1 := by
        rw [← hfi]
        exact Multiset.count_erase_self _ _
      rw [herase, hcount]
      simp [hi]
    · rw [ite_eq_right hfi]
      have herase : ((toPartition c).parts.erase (c.partSize j)).count i
          = (toPartition c).parts.count i :=
        Multiset.count_erase_of_ne (Ne.symm hfi) _
      rw [herase, hcount]
      simp [hi]

/-- Extending on the left lands in a given partition exactly when the
original partition is the given one with a part of size `1` removed. -/
private theorem extendLeft_eq_iff {n : ℕ} (c : OrderedFinpartition n)
    (π : Nat.Partition (n + 1)) :
    toPartition (c.extendLeft) = π ↔
      (toPartition c).parts = π.parts.erase 1 ∧ 1 ∈ π.parts := by
  constructor
  · intro h
    have hp := congrArg Nat.Partition.parts h
    rw [toPartition_extendLeft_parts] at hp
    refine ⟨?_, ?_⟩
    · have h2 := congrArg (fun m => m.erase 1) hp
      rwa [Multiset.erase_cons_head] at h2
    · rw [← hp]
      exact Multiset.mem_cons_self 1 _
  · rintro ⟨hparts, hmem⟩
    apply Nat.Partition.ext
    rw [toPartition_extendLeft_parts, hparts, Multiset.cons_erase hmem]

/-- Extending in the middle lands in a given partition exactly when the
original partition is the given one with one part of size `a` decremented to
`a - 1`, where `a` is one more than the size of the extended part. -/
private theorem extendMiddle_eq_iff {n : ℕ} (c : OrderedFinpartition n)
    (j : Fin c.length) (π : Nat.Partition (n + 1)) (a : ℕ)
    (ha : c.partSize j + 1 = a) :
    (toPartition (c.extendMiddle j) = π ∧ c.partSize j + 1 = a) ↔
      ((toPartition c).parts = (a - 1) ::ₘ π.parts.erase a ∧ c.partSize j = a - 1) := by
  constructor
  · rintro ⟨h, -⟩
    have hp := congrArg Nat.Partition.parts h
    rw [toPartition_extendMiddle_parts] at hp
    have hmem : c.partSize j ∈ (toPartition c).parts := by
      rw [toPartition_parts]
      have hj : j ∈ (Finset.univ : Finset (Fin c.length)).val := by
        rw [Finset.mem_val]
        exact Finset.mem_univ j
      exact Multiset.mem_map_of_mem _ hj
    have h2 := congrArg (fun m => m.erase (c.partSize j + 1)) hp
    rw [Multiset.erase_cons_head] at h2
    have hparts : (toPartition c).parts
        = c.partSize j ::ₘ (toPartition c).parts.erase (c.partSize j) :=
      (Multiset.cons_erase hmem).symm
    rw [h2] at hparts
    refine ⟨?_, by omega⟩
    rw [hparts, ← ha, Nat.add_sub_cancel]
  · rintro ⟨hparts, hsj⟩
    have hpos := c.partSize_pos j
    have hsumC := (toPartition c).parts_sum
    rw [hparts, Multiset.sum_cons] at hsumC
    have hmem : a ∈ π.parts := by
      by_contra hna
      rw [Multiset.erase_of_notMem hna] at hsumC
      have hsumP := π.parts_sum
      omega
    have ha1 : a - 1 + 1 = a := by omega
    refine ⟨?_, ha⟩
    apply Nat.Partition.ext
    rw [toPartition_extendMiddle_parts, hparts, hsj]
    have h3 : ((a - 1) ::ₘ π.parts.erase a).erase (a - 1) = π.parts.erase a :=
      Multiset.erase_cons_head _ _
    rw [h3, ha1, Multiset.cons_erase hmem]

/-- The number of ordered finpartitions with a given underlying integer
partition is the Bell number of its parts. -/
private theorem fiber_card_eq_bell : ∀ (n : ℕ) (π : Nat.Partition n),
    (Finset.univ.filter (fun c => toPartition c = π)).card = π.parts.bell := by
  intro n
  induction n with
  | zero =>
    intro π
    have hπ : π.parts = 0 := Nat.Partition.partition_zero_parts π
    have hfilter : (Finset.univ.filter
        (fun c : OrderedFinpartition 0 => toPartition c = π)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Nat.Partition.ext
      rw [hπ]
      simp [toPartition]
    rw [hfilter, Finset.card_univ, hπ, Multiset.bell_zero]
    exact Fintype.card_eq_one_iff.mpr ⟨default, fun x => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro π
    -- Step A: transport along `extendEquiv`.
    have hA : (Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => toPartition c = π)).card
        = (Finset.univ.filter
          (fun p : Σ c : OrderedFinpartition n, Option (Fin c.length) =>
            toPartition (p.1.extend p.2) = π)).card := by
      apply Finset.card_bij (fun c _ => (OrderedFinpartition.extendEquiv n).symm c)
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        rw [← OrderedFinpartition.extendEquiv_apply,
          Equiv.apply_symm_apply]
        exact hc
      · intro a _ b _ hab
        exact (OrderedFinpartition.extendEquiv n).symm.injective hab
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨(OrderedFinpartition.extendEquiv n) p, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [OrderedFinpartition.extendEquiv_apply]
          exact hp
        · exact Equiv.symm_apply_apply _ _
    -- Step B: regroup the sigma sum by the underlying partition.
    have hB : (Finset.univ.filter
        (fun p : Σ c : OrderedFinpartition n, Option (Fin c.length) =>
          toPartition (p.1.extend p.2) = π)).card
        = ∑ c : OrderedFinpartition n, (Finset.univ.filter
            (fun i : Option (Fin c.length) => toPartition (c.extend i) = π)).card := by
      rw [Finset.card_filter, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.card_filter]
    -- Step C: split the option sum.
    have hC : ∀ c : OrderedFinpartition n,
        (Finset.univ.filter
            (fun i : Option (Fin c.length) => toPartition (c.extend i) = π)).card
          = (if toPartition (c.extendLeft) = π then 1 else 0)
            + (Finset.univ.filter
                (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).card := by
      intro c
      have hsum : (Finset.univ.filter
          (fun i : Option (Fin c.length) => toPartition (c.extend i) = π)).card
          = ∑ i : Option (Fin c.length),
            (if toPartition (c.extend i) = π then 1 else 0) :=
        Finset.card_filter _ _
      rw [hsum, Fintype.sum_option]
      have h2 : (∑ j : Fin c.length,
          (if toPartition (c.extend (some j)) = π then 1 else 0))
          = (Finset.univ.filter
              (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl fun j _ => by
          rw [OrderedFinpartition.extend_some]
      rw [h2, OrderedFinpartition.extend_none]
    -- Step D: the left-extension contribution.
    have hNone : ∑ c : OrderedFinpartition n,
        (if toPartition (c.extendLeft) = π then 1 else 0)
        = if 1 ∈ π.parts then (π.parts.erase 1).bell else 0 := by
      have hsum : ∑ c : OrderedFinpartition n,
          (if toPartition (c.extendLeft) = π then 1 else 0)
          = (Finset.univ.filter
              (fun c : OrderedFinpartition n =>
                toPartition (c.extendLeft) = π)).card :=
        (Finset.card_filter _ _).symm
      rw [hsum]
      by_cases h1 : 1 ∈ π.parts
      · obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : Nat.Partition n,
          π₁.parts = π.parts.erase 1 :=
          ⟨⟨π.parts.erase 1,
            by intro i hi; exact π.parts_pos (π.parts.erase_subset 1 hi), by
              have h := congrArg Multiset.sum (Multiset.cons_erase h1)
              rw [Multiset.sum_cons] at h
              have hsumP := π.parts_sum
              omega⟩, rfl⟩
        simp only [h1, ite_true]
        have hfilter : (Finset.univ.filter
            (fun c : OrderedFinpartition n => toPartition (c.extendLeft) = π))
            = Finset.univ.filter (fun c => toPartition c = π₁) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [extendLeft_eq_iff]
          constructor
          · rintro ⟨hparts, -⟩
            apply Nat.Partition.ext
            rw [hπ₁]
            exact hparts
          · intro h
            have hp := congrArg Nat.Partition.parts h
            rw [hπ₁] at hp
            exact ⟨hp, h1⟩
        rw [hfilter, ih π₁, hπ₁]
      · simp only [h1, ite_false]
        have hempty : (Finset.univ.filter
            (fun c : OrderedFinpartition n =>
              toPartition (c.extendLeft) = π)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact h1 ((extendLeft_eq_iff c π).mp hc).2
        rw [hempty, Finset.card_empty]
    -- Step E: the middle-extension contribution, grouped by the size grown.
    have hSome : ∑ c : OrderedFinpartition n,
        (Finset.univ.filter
            (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).card
        = ∑ a ∈ π.parts.toFinset.erase 1,
            (((a - 1) ::ₘ π.parts.erase a).bell
              * ((a - 1) ::ₘ π.parts.erase a).count (a - 1)) := by
      have hstep : ∀ c : OrderedFinpartition n,
          (Finset.univ.filter
              (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).card
            = ∑ a ∈ π.parts.toFinset.erase 1,
                (if (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a
                 then ((a - 1) ::ₘ π.parts.erase a).count (a - 1) else 0) := by
        intro c
        have hmaps : Set.MapsTo (fun j => c.partSize j + 1)
            ↑(Finset.univ.filter
              (fun j : Fin c.length => toPartition (c.extendMiddle j) = π))
            ↑(π.parts.toFinset.erase 1) := by
          intro j hj
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hp := congrArg Nat.Partition.parts hj
          rw [toPartition_extendMiddle_parts] at hp
          have hmem : c.partSize j + 1 ∈ π.parts := by
            rw [← hp]
            exact Multiset.mem_cons_self _ _
          change c.partSize j + 1 ∈ π.parts.toFinset.erase 1
          refine Finset.mem_erase.mpr ⟨?_, Multiset.mem_toFinset.mpr hmem⟩
          have hpos := c.partSize_pos j
          omega
        rw [Finset.card_eq_sum_card_fiberwise hmaps]
        apply Finset.sum_congr rfl
        intro a ha
        have ha2 : 2 ≤ a := by
          have hne : a ≠ 1 := (Finset.mem_erase.mp ha).1
          have hpos : 0 < a :=
            π.parts_pos (Multiset.mem_toFinset.mp (Finset.mem_erase.mp ha).2)
          omega
        have hfiber : (Finset.univ.filter
            (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).filter
              (fun j => c.partSize j + 1 = a)
            = if (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a
              then Finset.univ.filter (fun j : Fin c.length => c.partSize j = a - 1)
              else ∅ := by
          split_ifs with hparts
          · ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hπ, haj⟩
              exact (extendMiddle_eq_iff c j π a haj).mp ⟨hπ, haj⟩ |>.2
            · intro hsj
              have haj : c.partSize j + 1 = a := by
                have hpos := c.partSize_pos j
                omega
              exact ⟨(extendMiddle_eq_iff c j π a haj).mpr ⟨hparts, hsj⟩ |>.1, haj⟩
          · apply Finset.eq_empty_iff_forall_notMem.mpr
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact hparts
              ((extendMiddle_eq_iff c j π a hj.2).mp ⟨hj.1, hj.2⟩ |>.1)
        rw [hfiber]
        split_ifs with hparts
        · rw [← toPartition_count c (a - 1), hparts]
        · simp
      rw [Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      have ha2 : 2 ≤ a := by
        have hmem : a ∈ π.parts := by
          simp only [Finset.mem_erase, Multiset.mem_toFinset] at ha
          exact ha.2
        have hpos := π.parts_pos hmem
        have hne : a ≠ 1 := by
          simp only [Finset.mem_erase, Multiset.mem_toFinset] at ha
          exact ha.1
        omega
      have hfilter : (Finset.univ.filter
          (fun c : OrderedFinpartition n =>
            (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a))
          = Finset.univ.filter (fun c : OrderedFinpartition n =>
              toPartition c =
                ⟨(a - 1) ::ₘ π.parts.erase a,
                  by
                    intro i hi
                    rcases Multiset.mem_cons.mp hi with rfl | hi
                    · omega
                    · exact π.parts_pos (Multiset.erase_subset a π.parts hi),
                  by
                    have h := congrArg Multiset.sum (Multiset.cons_erase
                      (by
                        have hmem : a ∈ π.parts := by
                          simp only [Finset.mem_erase, Multiset.mem_toFinset] at ha
                          exact ha.2
                        exact hmem))
                    rw [Multiset.sum_cons] at h
                    have hsumP := π.parts_sum
                    rw [Multiset.sum_cons]
                    omega⟩) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          apply Nat.Partition.ext
          exact h
        · intro h
          exact congrArg Nat.Partition.parts h
      have hcard : (Finset.univ.filter
          (fun c : OrderedFinpartition n =>
            (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a)).card
          = ((a - 1) ::ₘ π.parts.erase a).bell := by
        rw [hfilter]
        exact ih _
      have hsumK : (∑ c : OrderedFinpartition n,
          (if (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a
           then ((a - 1) ::ₘ π.parts.erase a).count (a - 1) else 0))
          = ((a - 1) ::ₘ π.parts.erase a).count (a - 1)
            * (Finset.univ.filter
                (fun c : OrderedFinpartition n =>
                  (toPartition c).parts = (a - 1) ::ₘ π.parts.erase a)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by
          split_ifs with h <;> simp
      rw [hsumK, hcard, mul_comm]
    -- Combine.
    have htotal : (Finset.univ.filter
        (fun c : OrderedFinpartition (n + 1) => toPartition c = π)).card
        = (if 1 ∈ π.parts then (π.parts.erase 1).bell else 0)
          + ∑ a ∈ π.parts.toFinset.erase 1,
              (((a - 1) ::ₘ π.parts.erase a).bell
                * ((a - 1) ::ₘ π.parts.erase a).count (a - 1)) := by
      calc (Finset.univ.filter
          (fun c : OrderedFinpartition (n + 1) => toPartition c = π)).card
          = ∑ c : OrderedFinpartition n, (Finset.univ.filter
              (fun i : Option (Fin c.length) => toPartition (c.extend i) = π)).card := by
            rw [hA, hB]
        _ = ∑ c : OrderedFinpartition n,
            ((if toPartition (c.extendLeft) = π then 1 else 0)
              + (Finset.univ.filter
                  (fun j : Fin c.length => toPartition (c.extendMiddle j) = π)).card) :=
          Finset.sum_congr rfl fun c _ => hC c
        _ = (∑ c : OrderedFinpartition n,
              (if toPartition (c.extendLeft) = π then 1 else 0))
            + (∑ c : OrderedFinpartition n,
                (Finset.univ.filter
                  (fun j : Fin c.length =>
                    toPartition (c.extendMiddle j) = π)).card) :=
          Finset.sum_add_distrib
        _ = _ := by rw [hNone, hSome]
    rw [htotal, Nat.bell_eq_sum_erase π]
    have hlarge : ∀ a ∈ π.parts.toFinset.erase 1,
        ((a - 1) ::ₘ π.parts.erase a).bell * ((a - 1) ::ₘ π.parts.erase a).count (a - 1)
          = n.choose (a - 1) * (π.parts.erase a).bell := by
      intro a ha
      obtain ⟨ha1, ha⟩ := Finset.mem_erase.mp ha
      have hmem := Multiset.mem_toFinset.mp ha
      have hpos := π.parts_pos hmem
      have hsum := Multiset.sum_erase hmem
      rw [π.parts_sum] at hsum
      rw [bell_cons_mul_count' _ (by omega : a - 1 ≠ 0),
        show (π.parts.erase a).sum + (a - 1) = n by omega]
    rw [Finset.sum_congr rfl hlarge]
    by_cases h1 : 1 ∈ π.parts
    · simpa [h1] using Finset.add_sum_erase π.parts.toFinset
        (fun a => n.choose (a - 1) * (π.parts.erase a).bell) (Multiset.mem_toFinset.mpr h1)
    · simp [h1]

/-- The factorial product over the parts of a partition, as a product over
`1 ≤ i ≤ n` of `(i !)` to the multiplicity of `i`. -/
private theorem map_factorial_prod_eq {n : ℕ} (π : Nat.Partition n) :
    (π.parts.map fun j => j.factorial).prod
      = ∏ i ∈ Finset.Icc 1 n, i.factorial ^ π.parts.count i := by
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset
  · intro j hj
    rw [Finset.mem_Icc]
    have hmem : j ∈ π.parts := Multiset.mem_toFinset.mp hj
    exact ⟨π.parts_pos hmem, Nat.Partition.le_of_mem_parts hmem⟩
  · intro j hj hjnot
    have hcount : π.parts.count j = 0 :=
      Multiset.count_eq_zero_of_notMem (by
        intro hmem
        exact hjnot (Multiset.mem_toFinset.mpr hmem))
    rw [hcount, pow_zero]

/-- The factorial-of-multiplicity product over the parts of a partition, as a
product over `1 ≤ i ≤ n`. -/
private theorem count_factorial_prod_eq {n : ℕ} (π : Nat.Partition n) :
    ∏ j ∈ π.parts.toFinset.erase 0, (π.parts.count j).factorial
      = ∏ i ∈ Finset.Icc 1 n, (π.parts.count i).factorial := by
  have h0 : π.parts.toFinset.erase 0 = π.parts.toFinset :=
    Finset.erase_eq_of_notMem (by
      simp only [Multiset.mem_toFinset]
      intro h
      exact Nat.lt_irrefl 0 (π.parts_pos h))
  rw [h0]
  apply Finset.prod_subset
  · intro j hj
    rw [Finset.mem_Icc]
    have hmem : j ∈ π.parts := Multiset.mem_toFinset.mp hj
    exact ⟨π.parts_pos hmem, Nat.Partition.le_of_mem_parts hmem⟩
  · intro j hj hjnot
    have hcount : π.parts.count j = 0 :=
      Multiset.count_eq_zero_of_notMem (by
        intro hmem
        exact hjnot (Multiset.mem_toFinset.mpr hmem))
    rw [hcount]
    simp

/-- Grouping the ordered-partition sum by the underlying integer partition. -/
private theorem ordered_sum_eq_bell_sum {n : ℕ} (A B : ℕ → ℝ) :
    ∑ c : OrderedFinpartition n, A c.length * ∏ j, B (c.partSize j)
      = ∑ π : Nat.Partition n, (π.parts.bell : ℝ) * A π.parts.card
          * ∏ i ∈ Finset.Icc 1 n, B i ^ π.parts.count i := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (f := fun c => A c.length * ∏ j, B (c.partSize j)) (g := toPartition)
    (s := Finset.univ) (t := Finset.univ) (fun c _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro π _
  have hterm : ∀ c ∈ Finset.univ.filter (fun c => toPartition c = π),
      A c.length * ∏ j, B (c.partSize j)
        = A π.parts.card * ∏ i ∈ Finset.Icc 1 n, B i ^ π.parts.count i := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [← hc, toPartition_card, prod_partSize_eq]
  calc ∑ c ∈ Finset.univ.filter (fun c => toPartition c = π),
        A c.length * ∏ j, B (c.partSize j)
      = ∑ _c ∈ Finset.univ.filter (fun c => toPartition c = π),
          A π.parts.card * ∏ i ∈ Finset.Icc 1 n, B i ^ π.parts.count i :=
        Finset.sum_congr rfl fun c hc => hterm c hc
    _ = ((Finset.univ.filter (fun c => toPartition c = π)).card : ℝ)
          * (A π.parts.card * ∏ i ∈ Finset.Icc 1 n, B i ^ π.parts.count i) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (π.parts.bell : ℝ) * A π.parts.card
          * ∏ i ∈ Finset.Icc 1 n, B i ^ π.parts.count i := by
        rw [fiber_card_eq_bell]
        ring

end taylorCoeff_comp_eq_sum_partitions

/-- **Faà di Bruno's formula for Taylor coefficients.** Let $f, g : \mathbb{R} \to \mathbb{R}$,
let $a \in \mathbb{R}$ and let $n$ be a natural number. Suppose that $g$ is $n$ times continuously
differentiable on a neighbourhood of $a$ and that $f$ is $n$ times continuously differentiable on a
neighbourhood of $g(a)$. For a partition $\pi$ of $n$, let $m_i(\pi)$ be the number of parts of
$\pi$ equal to $i$, and let $\ell(\pi) = m_1(\pi) + \cdots + m_n(\pi)$ be its number of parts. Then
$$\frac{(f \circ g)^{(n)}(a)}{n!} = \sum_{\pi} \frac{\ell(\pi)!}{\prod_{i=1}^{n} m_i(\pi)!} \cdot
\frac{f^{(\ell(\pi))}(g(a))}{\ell(\pi)!} \cdot
\prod_{i=1}^{n} \Bigl(\frac{g^{(i)}(a)}{i!}\Bigr)^{m_i(\pi)},$$
where the sum runs over all partitions $\pi$ of $n$.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Corollary 1 (quoted as Corollary 4 from the paper's reference [8]). -/
public theorem taylorCoeff_comp_eq_sum_partitions (f g : ℝ → ℝ) (a : ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f (g a)) (hg : ContDiffAt ℝ n g a) :
    iteratedDeriv n (f ∘ g) a / n.factorial =
      ∑ π : Nat.Partition n,
        ((π.parts.card.factorial : ℝ) /
            ∏ i ∈ Finset.Icc 1 n, ((π.parts.count i).factorial : ℝ)) *
          (iteratedDeriv π.parts.card f (g a) / π.parts.card.factorial) *
          ∏ i ∈ Finset.Icc 1 n, (iteratedDeriv i g a / i.factorial) ^ π.parts.count i := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hf hg le_rfl,
    taylorCoeff_comp_eq_sum_partitions.ordered_sum_eq_bell_sum
      (fun k => iteratedDeriv k f (g a)) (fun i => iteratedDeriv i g a)]
  have hnen : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [div_eq_iff hnen, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro π _
  have hbellR : (π.parts.bell : ℝ) = (n.factorial : ℝ) /
      ((∏ i ∈ Finset.Icc 1 n, ((i.factorial : ℕ) : ℝ) ^ π.parts.count i)
        * ∏ i ∈ Finset.Icc 1 n, ((π.parts.count i).factorial : ℝ)) := by
    have hD : ((π.parts.map fun j => j.factorial).prod
          * ∏ j ∈ π.parts.toFinset.erase 0, (π.parts.count j).factorial)
        = (∏ i ∈ Finset.Icc 1 n, i.factorial ^ π.parts.count i)
          * ∏ i ∈ Finset.Icc 1 n, (π.parts.count i).factorial := by
      rw [taylorCoeff_comp_eq_sum_partitions.map_factorial_prod_eq,
        taylorCoeff_comp_eq_sum_partitions.count_factorial_prod_eq]
    have hdvd : ((π.parts.map fun j => j.factorial).prod
          * ∏ j ∈ π.parts.toFinset.erase 0, (π.parts.count j).factorial)
          ∣ π.parts.sum.factorial :=
      ⟨π.parts.bell, by rw [← Multiset.bell_mul_eq]; ring⟩
    rw [Multiset.bell_eq, Nat.cast_div_charZero hdvd, π.parts_sum, hD]
    push_cast
    rfl
  have hQ : ∏ i ∈ Finset.Icc 1 n,
        (iteratedDeriv i g a / i.factorial) ^ π.parts.count i
        = (∏ i ∈ Finset.Icc 1 n, (iteratedDeriv i g a) ^ π.parts.count i)
          / ∏ i ∈ Finset.Icc 1 n, ((i.factorial : ℕ) : ℝ) ^ π.parts.count i := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [div_pow]
  have hneF : (∏ i ∈ Finset.Icc 1 n, ((i.factorial : ℕ) : ℝ) ^ π.parts.count i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))
  have hneM : (∏ i ∈ Finset.Icc 1 n, ((π.parts.count i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hneℓ : (π.parts.card.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hbellR, hQ]
  field_simp [hneF, hneM, hneℓ, hnen]

end MetaMathlibExt
