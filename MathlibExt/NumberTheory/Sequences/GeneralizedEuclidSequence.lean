/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped Pointwise

/-- Value of the `i`-th entry of a list, defaulting to `0` out of range. -/
private def eVal (l : List ℕ) (i : ℕ) : ℕ := l.getD i 0

private def geneuclidProduct (l : List ℕ) : ℕ :=
  ∏ i ∈ Finset.range l.length, eVal l i

private def geneuclidN (l : List ℕ) (I : Finset ℕ) : ℕ :=
  (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i

private def GeneuclidAppendable (l : List ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ I ⊆ Finset.range l.length, p ∣ geneuclidN l I

private def geneuclidResidues (q : ℕ) (l : List ℕ) : Finset (ZMod q) :=
  (Finset.range l.length).powerset.image fun I => ∏ i ∈ I, (eVal l i : ZMod q)

private def geneuclidUnits (q : ℕ) [NeZero q] (l : List ℕ) : Finset (ZMod q)ˣ :=
  Finset.univ.filter fun u => (u : ZMod q) ∈ geneuclidResidues q l

private theorem mem_geneuclidUnits_iff (q : ℕ) [NeZero q] (l : List ℕ) (u : (ZMod q)ˣ) :
    u ∈ geneuclidUnits q l ↔ (u : ZMod q) ∈ geneuclidResidues q l := by
  simp [geneuclidUnits]

private theorem mem_geneuclidResidues_iff (q : ℕ) (l : List ℕ) (x : ZMod q) :
    x ∈ geneuclidResidues q l ↔ ∃ I ⊆ Finset.range l.length,
      x = ∏ i ∈ I, (eVal l i : ZMod q) := by
  simp only [geneuclidResidues, Finset.mem_image, Finset.mem_powerset]
  aesop

private theorem eVal_lt (l : List ℕ) (i : ℕ) (h : i < l.length) : eVal l i = l[i] :=
  List.getD_eq_getElem l 0 h

private theorem geneuclidResidues_ne_zero (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqnot : q ∉ l) {x : ZMod q}
    (hx : x ∈ geneuclidResidues q l) : x ≠ 0 := by
  let _ : Fact q.Prime := ⟨hq⟩
  obtain ⟨I, hI, rfl⟩ := (mem_geneuclidResidues_iff q l x).mp hx
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hil : i < l.length := Finset.mem_range.mp (hI hi)
  rw [eVal_lt l i hil]
  intro hz
  have hdiv : q ∣ l[i] := (ZMod.natCast_eq_zero_iff l[i] q).mp hz
  have heq : q = l[i] :=
    (Nat.prime_dvd_prime_iff_eq hq (hprime l[i] (List.getElem_mem hil))).mp hdiv
  exact hqnot (heq ▸ List.getElem_mem hil)

private theorem eVal_prefix (l l' : List ℕ) (h : l <+: l') (i : ℕ) (hi : i < l.length) :
    eVal l i = eVal l' i := by
  unfold eVal
  rw [List.prefix_iff_eq_append] at h
  rw [← h]
  exact (List.getD_append l (List.drop l.length l') 0 i hi).symm

private theorem geneuclidResidues_append_subset (q : ℕ) (l : List ℕ) (r : ℕ) :
    geneuclidResidues q l ⊆ geneuclidResidues q (l ++ [r]) := by
  intro x hx
  obtain ⟨I, hI, rfl⟩ := (mem_geneuclidResidues_iff q l x).mp hx
  apply (mem_geneuclidResidues_iff q (l ++ [r]) _).mpr
  refine ⟨I, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_range, List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt (Finset.mem_range.mp (hI hi))
  · apply Finset.prod_congr rfl
    intro i hi
    rw [eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i
      (Finset.mem_range.mp (hI hi))]

private theorem geneuclidUnits_append_subset (q : ℕ) [NeZero q] (l : List ℕ) (r : ℕ) :
    geneuclidUnits q l ⊆ geneuclidUnits q (l ++ [r]) := by
  intro u hu
  rw [mem_geneuclidUnits_iff] at hu ⊢
  exact geneuclidResidues_append_subset q l r hu

private theorem geneuclidUnits_mul_mk0_mem_append (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ)
    (r : ℕ) (hr : (r : ZMod q) ≠ 0) (u : (ZMod q)ˣ) (hu : u ∈ geneuclidUnits q l) :
    u * Units.mk0 (r : ZMod q) hr ∈ geneuclidUnits q (l ++ [r]) := by
  rw [mem_geneuclidUnits_iff] at hu ⊢
  obtain ⟨I, hI, huI⟩ := (mem_geneuclidResidues_iff q l u).mp hu
  apply (mem_geneuclidResidues_iff q (l ++ [r]) _).mpr
  have hlast : l.length < (l ++ [r]).length := by simp
  have hnot : l.length ∉ I := fun h => (Finset.mem_range.mp (hI h)).false
  have hevalLast : eVal (l ++ [r]) l.length = r := by
    rw [eVal_lt _ _ hlast]
    simp
  have hprod : (∏ i ∈ I, (eVal (l ++ [r]) i : ZMod q)) =
      ∏ i ∈ I, (eVal l i : ZMod q) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i
      (Finset.mem_range.mp (hI hi))]
  refine ⟨insert l.length I, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_range]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hlast
    · exact (Finset.mem_range.mp (hI hi)).trans hlast
  · rw [Finset.prod_insert hnot, hevalLast]
    change (u : ZMod q) * r = r * ∏ i ∈ I, (eVal (l ++ [r]) i : ZMod q)
    rw [huI, hprod, mul_comm]

private theorem geneuclidProduct_split (l : List ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range l.length) :
    geneuclidProduct l =
      (∏ i ∈ I, eVal l i) * ∏ i ∈ (Finset.range l.length \ I), eVal l i := by
  rw [geneuclidProduct, ← Finset.prod_sdiff hI, mul_comm]

private theorem geneuclidProduct_append (l : List ℕ) (r : ℕ) :
    geneuclidProduct (l ++ [r]) = geneuclidProduct l * r := by
  rw [geneuclidProduct, List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact (eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i hi).symm
  · simp [eVal_lt]

private theorem geneuclid_unit_expression (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (u : (ZMod q)ˣ) (hu : u ∈ geneuclidUnits q l) :
    ∃ I ⊆ Finset.range l.length,
      (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) =
        (geneuclidN l I : ℕ) := by
  rw [mem_geneuclidUnits_iff] at hu
  obtain ⟨I, hI, huI⟩ := (mem_geneuclidResidues_iff q l u).mp hu
  refine ⟨I, hI, ?_⟩
  let A := ∏ i ∈ I, eVal l i
  let B := ∏ i ∈ (Finset.range l.length \ I), eVal l i
  have huA : (u : ZMod q) = (A : ZMod q) := by
    simpa [A] using huI
  have hA : (A : ZMod q) ≠ 0 := by
    rw [← huA]
    exact u.ne_zero
  have hprod : geneuclidProduct l = A * B := geneuclidProduct_split l I hI
  change (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) =
    ((A + B : ℕ) : ZMod q)
  rw [huA, hprod, Nat.cast_mul, mul_div_cancel_left₀ _ hA, Nat.cast_add]

private theorem geneuclid_q_appendable_iff_expression_zero (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l) :
    GeneuclidAppendable l q ↔ ∃ u ∈ geneuclidUnits q l,
      (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) = 0 := by
  constructor
  · rintro ⟨_hq, I, hI, hdiv⟩
    let A := ∏ i ∈ I, eVal l i
    have hA0 : (A : ZMod q) ≠ 0 := by
      apply geneuclidResidues_ne_zero l hprime q Fact.out hqnot
      apply (mem_geneuclidResidues_iff q l _).mpr
      refine ⟨I, hI, ?_⟩
      simp [A]
    let u := Units.mk0 (A : ZMod q) hA0
    have hu : u ∈ geneuclidUnits q l := by
      rw [mem_geneuclidUnits_iff]
      apply (mem_geneuclidResidues_iff q l _).mpr
      refine ⟨I, hI, ?_⟩
      simp [u, A]
    refine ⟨u, hu, ?_⟩
    have hcast : (geneuclidN l I : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mpr hdiv
    let B := ∏ i ∈ (Finset.range l.length \ I), eVal l i
    have hprod : geneuclidProduct l = A * B := geneuclidProduct_split l I hI
    change (A : ZMod q) + (geneuclidProduct l : ZMod q) / (A : ZMod q) = 0
    rw [hprod, Nat.cast_mul, mul_div_cancel_left₀ _ hA0, ← Nat.cast_add,
      show A + B = geneuclidN l I by rfl, hcast]
  · rintro ⟨u, hu, hzero⟩
    obtain ⟨I, hI, hExpr⟩ := geneuclid_unit_expression q l u hu
    refine ⟨Fact.out, I, hI, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mp
    rw [← hExpr, hzero]

private theorem geneuclid_not_squarefree_exists_sq_dvd {m : ℕ} (hm : ¬Squarefree m) :
    ∃ p, p.Prime ∧ p * p ∣ m := by
  rw [Nat.squarefree_iff_prime_squarefree] at hm
  push Not at hm
  obtain ⟨p, hp, hpdvd⟩ := hm
  exact ⟨p, hp, hpdvd⟩

private theorem geneuclid_odd_sq_recip_le (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℚ) / ((2 * k + 1 : ℕ) : ℚ) ^ 2 ≤
      (1 / 4 : ℚ) * (1 / (k : ℚ) - 1 / ((k + 1 : ℕ) : ℚ)) := by
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hk)
  have hk10 : (0 : ℚ) < k + 1 := by positivity
  have hodd0 : (0 : ℚ) < 2 * k + 1 := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul] at *
  field_simp
  nlinarith

private theorem geneuclid_recip_telescope (M : ℕ) :
    (∑ k ∈ Finset.range M,
      ((1 : ℚ) / ((k + 2 : ℕ) : ℚ) - 1 / ((k + 3 : ℕ) : ℚ))) =
        1 / 2 - 1 / ((M + 2 : ℕ) : ℚ) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]

private theorem geneuclid_odd_sq_sum_le (M : ℕ) :
    (∑ k ∈ Finset.range M, (1 : ℚ) / ((2 * (k + 2) + 1 : ℕ) : ℚ) ^ 2) ≤ 1 / 8 := by
  calc
    _ ≤ ∑ k ∈ Finset.range M, (1 / 4 : ℚ) *
        (1 / ((k + 2 : ℕ) : ℚ) - 1 / ((k + 3 : ℕ) : ℚ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact geneuclid_odd_sq_recip_le (k + 2) (by omega)
    _ = (1 / 4 : ℚ) * (1 / 2 - 1 / ((M + 2 : ℕ) : ℚ)) := by
      rw [← Finset.mul_sum, geneuclid_recip_telescope]
    _ ≤ 1 / 8 := by
      have hden : (0 : ℚ) < ((M + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < M + 2)
      have hinv : (0 : ℚ) ≤ 1 / ((M + 2 : ℕ) : ℚ) := (one_div_pos.mpr hden).le
      calc
        _ ≤ (1 / 4 : ℚ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ hinv) (by norm_num)
        _ = 1 / 8 := by norm_num

private def geneuclidBad (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun e => ¬Squarefree (e + 1)

private def geneuclidMultiples (N k : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun e => k ∣ e + 1

private theorem geneuclid_odd_half_ge_two {p k : ℕ} (hp : 2 ≤ p) (hp3 : p ≠ 3)
    (hk : p = 2 * k + 1) : 2 ≤ k := by
  omega

private theorem geneuclidBad_subset_square_multiples (N : ℕ) :
    geneuclidBad N ⊆ geneuclidMultiples N 4 ∪
      (geneuclidMultiples N 9 ∪ (Finset.range N).biUnion fun j =>
        geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)) := by
  intro e he
  rw [geneuclidBad, Finset.mem_filter] at he
  obtain ⟨p, hp, hpdvd⟩ := geneuclid_not_squarefree_exists_sq_dvd he.2
  have hsquare_le : p * p ≤ e + 1 := Nat.le_of_dvd (by omega) hpdvd
  have heN : e + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp he.1)
  have hp_le_square : p ≤ p * p := by
    nth_rewrite 1 [← Nat.mul_one p]
    exact Nat.mul_le_mul_left p hp.one_le
  have hpN : p ≤ N := hp_le_square.trans (hsquare_le.trans heN)
  rw [Finset.mem_union]
  by_cases hp2 : p = 2
  · left
    subst p
    exact Finset.mem_filter.mpr ⟨he.1, by norm_num at hpdvd ⊢; exact hpdvd⟩
  · right
    rw [Finset.mem_union]
    by_cases hp3 : p = 3
    · left
      subst p
      exact Finset.mem_filter.mpr ⟨he.1, by norm_num at hpdvd ⊢; exact hpdvd⟩
    · right
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      rw [Finset.mem_biUnion]
      have hjN : k - 2 < N := by omega
      refine ⟨k - 2, Finset.mem_range.mpr hjN, ?_⟩
      rw [geneuclidMultiples, Finset.mem_filter]
      refine ⟨he.1, ?_⟩
      have hk2 : 2 ≤ k := geneuclid_odd_half_ge_two hp.two_le hp3 hk
      have hbase : 2 * (k - 2 + 2) + 1 = p := by
        rw [Nat.sub_add_cancel hk2, hk]
      simpa [pow_two, hbase] using hpdvd

private theorem geneuclidBad_card_le (N : ℕ) :
    (geneuclidBad N).card ≤ N / 4 + N / 9 +
      ∑ j ∈ Finset.range N, N / (2 * (j + 2) + 1) ^ 2 := by
  let A := geneuclidMultiples N 4
  let B := geneuclidMultiples N 9
  let C := (Finset.range N).biUnion fun j =>
    geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)
  have hsub : geneuclidBad N ⊆ A ∪ (B ∪ C) := geneuclidBad_subset_square_multiples N
  have hC : C.card ≤ ∑ j ∈ Finset.range N,
      (geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)).card :=
    Finset.card_biUnion_le
  calc
    (geneuclidBad N).card ≤ (A ∪ (B ∪ C)).card := Finset.card_le_card hsub
    _ ≤ A.card + (B ∪ C).card := Finset.card_union_le A (B ∪ C)
    _ ≤ A.card + (B.card + C.card) :=
      Nat.add_le_add_left (Finset.card_union_le B C) A.card
    _ ≤ A.card + (B.card + ∑ j ∈ Finset.range N,
        (geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)).card) :=
      Nat.add_le_add_left (Nat.add_le_add_left hC B.card) A.card
    _ = N / 4 + N / 9 + ∑ j ∈ Finset.range N, N / (2 * (j + 2) + 1) ^ 2 := by
      simp only [A, B, geneuclidMultiples, Nat.card_multiples]
      omega

private theorem geneuclidBad_cast_le (N : ℕ) :
    ((geneuclidBad N).card : ℚ) ≤
      (N : ℚ) * ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) := by
  have hbad : ((geneuclidBad N).card : ℚ) ≤
      ((N / 4 + N / 9 + ∑ j ∈ Finset.range N,
        N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := by
    exact_mod_cast geneuclidBad_card_le N
  have h4 : ((N / 4 : ℕ) : ℚ) ≤ (N : ℚ) / 4 := Nat.cast_div_le
  have h9 : ((N / 9 : ℕ) : ℚ) ≤ (N : ℚ) / 9 := Nat.cast_div_le
  have hsum : (∑ j ∈ Finset.range N,
      ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ)) ≤
      (N : ℚ) * (1 / 8) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          (N : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) ≤
              (N : ℚ) / (((2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := Nat.cast_div_le
          _ = (N : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
            rw [Nat.cast_pow]
      _ = (N : ℚ) * ∑ j ∈ Finset.range N,
          (1 : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp
      _ ≤ (N : ℚ) * (1 / 8) := by
        exact mul_le_mul_of_nonneg_left (geneuclid_odd_sq_sum_le N) (by positivity)
  calc
    _ ≤ ((N / 4 : ℕ) : ℚ) + ((N / 9 : ℕ) : ℚ) +
        ∑ j ∈ Finset.range N, ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := by
      simpa only [Nat.cast_add, Nat.cast_sum] using hbad
    _ ≤ (N : ℚ) / 4 + (N : ℚ) / 9 + (N : ℚ) * (1 / 8) :=
      add_le_add (add_le_add h4 h9) hsum
    _ = (N : ℚ) * ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) := by ring

private theorem geneuclid_squarefree_majority (N : ℕ) (hN : 0 < N) :
    N < 2 * ((Finset.range N).filter fun e => Squarefree (e + 1)).card := by
  let good := (Finset.range N).filter fun e => Squarefree (e + 1)
  have hgood : good ⊆ Finset.range N := Finset.filter_subset _ _
  have hbad_eq : geneuclidBad N = Finset.range N \ good := by
    ext e
    simp [geneuclidBad, good]
    aesop
  have hcards : (geneuclidBad N).card + good.card = N := by
    have hgoodcard : good.card ≤ N := by simpa using Finset.card_le_card hgood
    rw [hbad_eq, Finset.card_sdiff_of_subset hgood, Finset.card_range]
    omega
  have hcoef : ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) < 1 / 2 := by norm_num
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hbad_lt : ((geneuclidBad N).card : ℚ) < (N : ℚ) * (1 / 2) :=
    (geneuclidBad_cast_le N).trans_lt (mul_lt_mul_of_pos_left hcoef hNq)
  have hbad_nat : 2 * (geneuclidBad N).card < N := by
    have hbad_lt' : (2 * (geneuclidBad N).card : ℚ) < N := by
      norm_num at hbad_lt ⊢
      linarith
    exact_mod_cast hbad_lt'
  change N < 2 * good.card
  omega

private theorem geneuclid_squarefree_mem_units_of_primeFactors (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) (d : ℕ)
    (hd0 : (d : ZMod q) ≠ 0) (hdsq : Squarefree d)
    (hfac : ∀ p ∈ d.primeFactors, p < q) :
    Units.mk0 (d : ZMod q) hd0 ∈ geneuclidUnits q l := by
  rw [mem_geneuclidUnits_iff]
  apply (mem_geneuclidResidues_iff q l _).mpr
  let I := d.primeFactors.image fun p => l.idxOf p
  have hmem (p : ℕ) (hp : p ∈ d.primeFactors) : p ∈ l := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    exact hmin p hpprime (hfac p hp)
  have hI : I ⊆ Finset.range l.length := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (List.idxOf_lt_length_iff.mpr (hmem p hp))
  refine ⟨I, hI, ?_⟩
  change (d : ZMod q) = ∏ i ∈ I, (eVal l i : ZMod q)
  have hinj : Set.InjOn (fun p => l.idxOf p) d.primeFactors := by
    intro p hp r hr hpr
    exact (List.idxOf_inj (hmem p hp)).mp hpr
  simp only [I]
  rw [Finset.prod_image hinj]
  have heval : ∀ p ∈ d.primeFactors, eVal l (l.idxOf p) = p := by
    intro p hp
    rw [eVal_lt l (l.idxOf p) (List.idxOf_lt_length_iff.mpr (hmem p hp))]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem p hp))
  rw [Finset.prod_congr rfl fun p hp => congrArg (fun n : ℕ => (n : ZMod q)) (heval p hp)]
  simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ZMod q))
    (Nat.prod_primeFactors_of_squarefree hdsq).symm

private theorem geneuclid_squarefree_mem_units (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) (d : ℕ)
    (hdpos : 0 < d) (hdlt : d < q) (hdsq : Squarefree d) :
    Units.mk0 (d : ZMod q) (by
      intro hd0
      have hqd : q ∣ d := (ZMod.natCast_eq_zero_iff d q).mp hd0
      exact (not_le_of_gt hdlt) (Nat.le_of_dvd hdpos hqd)) ∈ geneuclidUnits q l := by
  apply geneuclid_squarefree_mem_units_of_primeFactors q l hmin d
  · exact hdsq
  · intro p hp
    exact (Nat.le_of_dvd hdpos (Nat.dvd_of_mem_primeFactors hp)).trans_lt hdlt

private def geneuclidUnitOfNat (q : ℕ) [Fact q.Prime] [NeZero q]
    (d : ℕ) (hqd : ¬q ∣ d) : (ZMod q)ˣ :=
  Units.mk0 (d : ZMod q) (mt (ZMod.natCast_eq_zero_iff d q).mp hqd)

private def geneuclidSevenRepresentatives : Finset (Units (ZMod 7)) :=
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : NeZero 7 := ⟨by decide⟩
  {geneuclidUnitOfNat 7 1 (by norm_num), geneuclidUnitOfNat 7 2 (by norm_num),
    geneuclidUnitOfNat 7 3 (by norm_num), geneuclidUnitOfNat 7 5 (by norm_num),
    geneuclidUnitOfNat 7 6 (by norm_num)}

private theorem geneuclidSevenRepresentatives_card : geneuclidSevenRepresentatives.card = 5 := by
  decide

private def geneuclidThirteenRepresentatives : Finset (Units (ZMod 13)) :=
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  let _ : NeZero 13 := ⟨by decide⟩
  {geneuclidUnitOfNat 13 1 (by norm_num), geneuclidUnitOfNat 13 15 (by norm_num),
    geneuclidUnitOfNat 13 55 (by norm_num), geneuclidUnitOfNat 13 30 (by norm_num),
    geneuclidUnitOfNat 13 5 (by norm_num), geneuclidUnitOfNat 13 110 (by norm_num),
    geneuclidUnitOfNat 13 7 (by norm_num), geneuclidUnitOfNat 13 385 (by norm_num),
    geneuclidUnitOfNat 13 35 (by norm_num), geneuclidUnitOfNat 13 231 (by norm_num),
    geneuclidUnitOfNat 13 11 (by norm_num), geneuclidUnitOfNat 13 77 (by norm_num)}

private theorem geneuclidThirteenRepresentatives_card :
    geneuclidThirteenRepresentatives.card = 12 := by
  decide

private theorem geneuclid_squarefree_thirty : Squarefree 30 := by
  rw [show 30 = (2 * 3) * 5 by norm_num, Nat.squarefree_mul (by decide),
    Nat.squarefree_mul (by decide)]
  exact ⟨⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩,
    Nat.prime_five.squarefree⟩

private theorem geneuclid_squarefree_two_thousand_three_hundred_ten : Squarefree 2310 := by
  rw [show 2310 = (((2 * 3) * 5) * 7) * 11 by norm_num,
    Nat.squarefree_mul (by decide), Nat.squarefree_mul (by decide),
    Nat.squarefree_mul (by decide), Nat.squarefree_mul (by decide)]
  exact ⟨⟨⟨⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩,
    Nat.prime_five.squarefree⟩, Nat.prime_seven.squarefree⟩,
    Nat.prime_eleven.squarefree⟩

private theorem geneuclid_prime_lt_seven_of_dvd_thirty {p : ℕ} (hp : p.Prime)
    (h : p ∣ 30) : p < 7 := by
  rw [show 30 = (2 * 3) * 5 by norm_num, hp.dvd_mul, hp.dvd_mul] at h
  rcases h with (h | h) | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h]
    norm_num

private theorem geneuclid_prime_lt_thirteen_of_dvd_primorial {p : ℕ} (hp : p.Prime)
    (h : p ∣ 2310) : p < 13 := by
  rw [show 2310 = (((2 * 3) * 5) * 7) * 11 by norm_num,
    hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at h
  rcases h with (((h | h) | h) | h) | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_eleven).mp h]
    norm_num

private theorem geneuclidSevenRepresentatives_subset [Fact (Nat.Prime 7)] [NeZero 7]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < 7 → p ∈ l) :
    geneuclidSevenRepresentatives ⊆ geneuclidUnits 7 l := by
  intro u hu
  simp only [geneuclidSevenRepresentatives, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply geneuclid_squarefree_mem_units_of_primeFactors 7 l hmin
    · apply geneuclid_squarefree_thirty.squarefree_of_dvd
      norm_num
    · intro p hp
      apply geneuclid_prime_lt_seven_of_dvd_thirty (Nat.prime_of_mem_primeFactors hp)
      exact (Nat.dvd_of_mem_primeFactors hp).trans (by norm_num)

private theorem geneuclidThirteenRepresentatives_subset [Fact (Nat.Prime 13)] [NeZero 13]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < 13 → p ∈ l) :
    geneuclidThirteenRepresentatives ⊆ geneuclidUnits 13 l := by
  intro u hu
  simp only [geneuclidThirteenRepresentatives, Finset.mem_insert,
    Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply geneuclid_squarefree_mem_units_of_primeFactors 13 l hmin
    · apply geneuclid_squarefree_two_thousand_three_hundred_ten.squarefree_of_dvd
      norm_num
    · intro p hp
      apply geneuclid_prime_lt_thirteen_of_dvd_primorial
        (Nat.prime_of_mem_primeFactors hp)
      exact (Nat.dvd_of_mem_primeFactors hp).trans (by norm_num)

private theorem geneuclidUnits_large (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) :
    q - 1 < 2 * (geneuclidUnits q l).card := by
  let good := (Finset.range (q - 1)).filter fun e => Squarefree (e + 1)
  have hq3 : 3 ≤ q := by
    have hq := (Fact.out : q.Prime).two_le
    omega
  let f : {e // e ∈ good} → {u // u ∈ geneuclidUnits q l} := fun e =>
    let heRange : e.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    let hdlt : e.1 + 1 < q := by omega
    let hd0 : ((e.1 + 1 : ℕ) : ZMod q) ≠ 0 := by
      intro hz
      have hqd : q ∣ e.1 + 1 := (ZMod.natCast_eq_zero_iff (e.1 + 1) q).mp hz
      exact (not_le_of_gt hdlt) (Nat.le_of_dvd (by omega) hqd)
    ⟨Units.mk0 ((e.1 + 1 : ℕ) : ZMod q) hd0,
      geneuclid_squarefree_mem_units q l hmin (e.1 + 1) (by omega) hdlt
        (Finset.mem_filter.mp e.2).2⟩
  have hf : Function.Injective f := by
    intro e r her
    apply Subtype.ext
    have hval := congrArg Units.val (congrArg Subtype.val her)
    have heRange : e.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    have hrRange : r.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp r.2).1
    have heq : e.1 + 1 < q := by omega
    have hrq : r.1 + 1 < q := by omega
    simp only [f, Units.val_mk0] at hval
    have hval' := congrArg ZMod.val hval
    rw [ZMod.val_natCast_of_lt heq, ZMod.val_natCast_of_lt hrq] at hval'
    omega
  have hcard : good.card ≤ (geneuclidUnits q l).card :=
    Finset.card_le_card_of_injective hf
  have hmajor := geneuclid_squarefree_majority (q - 1) (by omega)
  change q - 1 < 2 * good.card at hmajor
  omega

private def geneuclidQuadChar (q : ℕ) [Fact q.Prime] [NeZero q] :
    MulChar (ZMod q) ℂ :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

private theorem geneuclidQuadChar_ne_one (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) : geneuclidQuadChar q ≠ 1 := by
  rw [geneuclidQuadChar, MulChar.ringHomComp_ne_one_iff]
  · exact quadraticChar_ne_one (by rwa [ZMod.ringChar_zmod_n])
  · exact Int.cast_injective

private theorem geneuclidQuadChar_isQuadratic (q : ℕ) [Fact q.Prime] [NeZero q] :
    (geneuclidQuadChar q).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)

private theorem geneuclidQuadChar_neg_one_of_mod_four_one (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq2 : q ≠ 2) (hq4 : q % 4 = 1) :
    geneuclidQuadChar q (-1) = 1 := by
  change ((quadraticChar (ZMod q)) (-1) : ℂ) = 1
  rw [quadraticChar_neg_one ((ZMod.ringChar_zmod_n q).substr hq2), ZMod.card,
    ZMod.χ₄_nat_one_mod_four hq4]
  norm_num

private theorem geneuclidQuadChar_neg_one_of_mod_four_three (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq2 : q ≠ 2) (hq4 : q % 4 = 3) :
    geneuclidQuadChar q (-1) = -1 := by
  change ((quadraticChar (ZMod q)) (-1) : ℂ) = -1
  rw [quadraticChar_neg_one ((ZMod.ringChar_zmod_n q).substr hq2), ZMod.card,
    ZMod.χ₄_nat_three_mod_four hq4]
  norm_num

private theorem geneuclid_norm_jacobiSum (q : ℕ) [Fact q.Prime] [NeZero q]
    {χ φ : MulChar (ZMod q) ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ = Real.sqrt q := by
  have hchar : ringChar ℂ ≠ ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]
    simp only [ringChar.eq_zero]
    exact (Fact.out : q.Prime).ne_zero.symm
  have hj := jacobiSum_mul_jacobiSum_inv hchar hχ hφ hχφ
  have hstar : star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
    rw [jacobiSum, jacobiSum]
    change (starRingEnd ℂ) (∑ x, χ x * φ (1 - x)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [map_mul]
    change star (χ x) * star (φ (1 - x)) = _
    rw [MulChar.star_apply', MulChar.star_apply']
  rw [← hstar] at hj
  change jacobiSum χ φ * (starRingEnd ℂ) (jacobiSum χ φ) = _ at hj
  rw [Complex.mul_conj, ZMod.card] at hj
  have hjreal : Complex.normSq (jacobiSum χ φ) = (q : ℝ) := by
    exact_mod_cast hj
  have hnorm : ‖jacobiSum χ φ‖ ^ 2 = (q : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, hjreal]
  have hsqrt : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (jacobiSum χ φ), Real.sqrt_nonneg (q : ℝ)]

private theorem geneuclid_norm_mulChar_apply (q : ℕ) [Fact q.Prime] [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (x : ZMod q) (hx : x ≠ 0) : ‖χ x‖ = 1 := by
  let u : (ZMod q)ˣ := Units.mk0 x hx
  simpa only [MulChar.coe_equivToUnitHom, u, Units.val_mk0] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

private theorem geneuclid_mulChar_add_sum (q : ℕ) [Fact q.Prime] [NeZero q]
    (ψ χ : MulChar (ZMod q) ℂ) (a : ZMod q) (ha : a ≠ 0) :
    (∑ u : ZMod q, ψ u * χ (u + a)) = ψ (-a) * χ a * jacobiSum ψ χ := by
  calc
    _ = ∑ u : ZMod q, ψ ((Equiv.mulLeft₀ (-a) (neg_ne_zero.mpr ha)) u) *
        χ ((Equiv.mulLeft₀ (-a) (neg_ne_zero.mpr ha)) u + a) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ (-a) (neg_ne_zero.mpr ha))
        (fun u => ψ u * χ (u + a))).symm
    _ = ∑ u : ZMod q, (ψ (-a) * χ a) * (ψ u * χ (1 - u)) := by
      simp only [Equiv.mulLeft₀_apply]
      apply Finset.sum_congr rfl
      intro u hu
      rw [show -a * u + a = a * (1 - u) by ring, map_mul, map_mul]
      ring
    _ = ψ (-a) * χ a * ∑ u : ZMod q, ψ u * χ (1 - u) := by
      rw [Finset.mul_sum]
    _ = ψ (-a) * χ a * jacobiSum ψ χ := by rw [jacobiSum]

private theorem geneuclid_quadratic_mulChar_unique {F : Type*} [CommMonoid F]
    [IsCyclic Fˣ] {χ φ : MulChar F ℂ} (hχsq : χ ^ 2 = 1) (hφsq : φ ^ 2 = 1)
    (hχ : χ ≠ 1) (hφ : φ ≠ 1) : χ = φ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  apply (MulChar.eq_iff hg χ φ).mpr
  have hχg_sq : χ g ^ 2 = 1 := by
    have h := congrArg (fun θ : MulChar F ℂ => θ g) hχsq
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  have hφg_sq : φ g ^ 2 = 1 := by
    have h := congrArg (fun θ : MulChar F ℂ => θ g) hφsq
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h
  have hχg_ne : χ g ≠ 1 := by
    intro h
    apply hχ
    apply (MulChar.eq_iff hg χ 1).mpr
    simpa only [MulChar.one_apply_coe] using h
  have hφg_ne : φ g ≠ 1 := by
    intro h
    apply hφ
    apply (MulChar.eq_iff hg φ 1).mpr
    simpa only [MulChar.one_apply_coe] using h
  rcases sq_eq_one_iff.mp hχg_sq with hχg | hχg
  · exact (hχg_ne hχg).elim
  · rcases sq_eq_one_iff.mp hφg_sq with hφg | hφg
    · exact (hφg_ne hφg).elim
    · rw [hχg, hφg]

private theorem geneuclid_exists_quartic_char (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (hq4 : q % 4 = 1) :
    ∃ lam : MulChar (ZMod q) ℂ, orderOf lam = 4 ∧ lam ^ 2 = geneuclidQuadChar q := by
  have hdiv : 4 ∣ q - 1 := by omega
  have hdiv' : 4 ∣ Fintype.card (ZMod q) - 1 := by simpa only [ZMod.card] using hdiv
  obtain ⟨lam, hlamOrder⟩ :=
    MulChar.exists_mulChar_orderOf (ZMod q) hdiv' Complex.isPrimitiveRoot_I
  have hlamSqNe : lam ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf lam ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hlamOrder] at hdvd
    norm_num at hdvd
  have hlamSqSq : (lam ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← hlamOrder, pow_orderOf_eq_one]
  have hχsq : (geneuclidQuadChar q) ^ 2 = 1 :=
    (geneuclidQuadChar_isQuadratic q).sq_eq_one
  exact ⟨lam, hlamOrder,
    geneuclid_quadratic_mulChar_unique hlamSqSq hχsq hlamSqNe
      (geneuclidQuadChar_ne_one q hq2)⟩

private theorem geneuclid_quartic_fiber_sum (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (hq4 : q % 4 = 1) (lam : MulChar (ZMod q) ℂ)
    (hlam : lam ^ 2 = geneuclidQuadChar q) (u : ZMod q) :
    (∑ x ∈ Finset.univ.filter (fun x : ZMod q => x ^ 2 = u), geneuclidQuadChar q x) =
      lam u + (lam ^ 3) u := by
  by_cases hu0 : u = 0
  · subst u
    have hfilter : Finset.univ.filter (fun x : ZMod q => x ^ 2 = 0) = {0} := by
      ext x
      simp
    rw [hfilter, Finset.sum_singleton]
    rw [(geneuclidQuadChar q).map_zero, lam.map_zero, (lam ^ 3).map_zero, add_zero]
  by_cases huSq : IsSquare u
  · obtain ⟨y, rfl⟩ := huSq
    have hy0 : y ≠ 0 := by
      intro hy
      subst y
      simp at hu0
    have htwo : (2 : ZMod q) ≠ 0 := by
      intro h
      have hqd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
      exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp hqd)
    have hyneg : y ≠ -y := by
      intro hy
      have hsum : y + y = 0 := eq_neg_iff_add_eq_zero.mp hy
      have hprod : (2 : ZMod q) * y = 0 := by simpa [two_mul] using hsum
      exact hy0 ((mul_eq_zero.mp hprod).resolve_left htwo)
    have hfilter : Finset.univ.filter (fun x : ZMod q => x ^ 2 = y * y) = {y, -y} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      simpa only [pow_two] using (sq_eq_sq_iff_eq_or_eq_neg (a := x) (b := y))
    rw [hfilter, Finset.sum_pair hyneg]
    have hχneg : geneuclidQuadChar q (-y) = geneuclidQuadChar q y := by
      rw [show -y = (-1) * y by ring, map_mul,
        geneuclidQuadChar_neg_one_of_mod_four_one q hq2 hq4, one_mul]
    have hlamY : lam y ^ 2 = geneuclidQuadChar q y := by
      have h := congrArg (fun χ : MulChar (ZMod q) ℂ => χ y) hlam
      rw [MulChar.pow_apply' lam (by norm_num) y] at h
      exact h
    have hχYsq : geneuclidQuadChar q y ^ 2 = 1 := by
      have h := congrArg (fun χ : MulChar (ZMod q) ℂ => χ y)
        (geneuclidQuadChar_isQuadratic q).sq_eq_one
      rw [MulChar.pow_apply' (geneuclidQuadChar q) (by norm_num) y,
        MulChar.one_apply hy0.isUnit] at h
      exact h
    have hχYcube : geneuclidQuadChar q y ^ 3 = geneuclidQuadChar q y := by
      calc
        _ = geneuclidQuadChar q y ^ 2 * geneuclidQuadChar q y := by ring
        _ = _ := by rw [hχYsq, one_mul]
    rw [hχneg]
    have hlam3Y : (lam ^ 3) y = lam y ^ 3 := MulChar.pow_apply' lam (by norm_num) y
    simp only [map_mul, hlam3Y]
    rw [show lam y * lam y = lam y ^ 2 by ring, hlamY]
    rw [show lam y ^ 3 * lam y ^ 3 = (lam y ^ 2) ^ 3 by ring, hlamY, hχYcube]
  · have hfilter : Finset.univ.filter (fun x : ZMod q => x ^ 2 = u) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hx
      apply huSq
      exact ⟨x, by simpa only [pow_two] using hx.symm⟩
    rw [hfilter, Finset.sum_empty]
    have hlamU : lam u ^ 2 = geneuclidQuadChar q u := by
      have h := congrArg (fun χ : MulChar (ZMod q) ℂ => χ u) hlam
      rw [MulChar.pow_apply' lam (by norm_num) u] at h
      exact h
    have hχU : geneuclidQuadChar q u = -1 := by
      change ((quadraticChar (ZMod q)) u : ℂ) = -1
      exact_mod_cast quadraticChar_neg_one_iff_not_isSquare.mpr huSq
    rw [MulChar.pow_apply' lam (by norm_num) u]
    calc
      0 = lam u * (1 + lam u ^ 2) := by rw [hlamU, hχU]; ring
      _ = lam u + lam u ^ 3 := by ring

private theorem geneuclid_quartic_sum_eq (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (hq4 : q % 4 = 1) (lam : MulChar (ZMod q) ℂ)
    (hlam : lam ^ 2 = geneuclidQuadChar q) (a : ZMod q) :
    (∑ x : ZMod q, geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a)) =
      ∑ u : ZMod q, (lam u + (lam ^ 3) u) * geneuclidQuadChar q (u + a) := by
  calc
    _ = ∑ u : ZMod q, ∑ x ∈ Finset.univ with x ^ 2 = u,
        geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a) := by
      symm
      simpa using
        (Finset.sum_fiberwise Finset.univ (fun x : ZMod q => x ^ 2)
          (fun x => geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a)))
    _ = ∑ u : ZMod q, (lam u + (lam ^ 3) u) * geneuclidQuadChar q (u + a) := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        _ = ∑ x ∈ Finset.univ.filter (fun x : ZMod q => x ^ 2 = u),
            geneuclidQuadChar q x * geneuclidQuadChar q (u + a) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [hx.2]
        _ = (∑ x ∈ Finset.univ.filter (fun x : ZMod q => x ^ 2 = u),
            geneuclidQuadChar q x) * geneuclidQuadChar q (u + a) := by
          rw [Finset.sum_mul]
        _ = (lam u + (lam ^ 3) u) * geneuclidQuadChar q (u + a) := by
          rw [geneuclid_quartic_fiber_sum q hq2 hq4 lam hlam u]

private theorem geneuclid_quartic_sum_norm_le (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (hq4 : q % 4 = 1) (a : ZMod q) (ha : a ≠ 0) :
    ‖∑ x : ZMod q, geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a)‖ ≤
      2 * Real.sqrt q := by
  obtain ⟨lam, hlamOrder, hlamSq⟩ := geneuclid_exists_quartic_char q hq2 hq4
  have hlamPowNe (k : ℕ) (hk : ¬4 ∣ k) : lam ^ k ≠ 1 := by
    intro h
    apply hk
    rw [← hlamOrder]
    exact orderOf_dvd_of_pow_eq_one h
  have hlamNe : lam ≠ 1 := by
    simpa only [pow_one] using hlamPowNe 1 (by norm_num)
  have hlam3Ne : lam ^ 3 ≠ 1 := hlamPowNe 3 (by norm_num)
  have hχNe : geneuclidQuadChar q ≠ 1 := geneuclidQuadChar_ne_one q hq2
  have hprod1eq : lam * geneuclidQuadChar q = lam ^ 3 := by
    rw [← hlamSq]
    simp [pow_succ, mul_comm]
  have hprod3eq : lam ^ 3 * geneuclidQuadChar q = lam ^ 5 := by
    rw [← hlamSq, ← pow_add]
  have hprod1 : lam * geneuclidQuadChar q ≠ 1 := by rwa [hprod1eq]
  have hprod3 : lam ^ 3 * geneuclidQuadChar q ≠ 1 := by
    rw [hprod3eq]
    exact hlamPowNe 5 (by norm_num)
  rw [geneuclid_quartic_sum_eq q hq2 hq4 lam hlamSq a]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, geneuclid_mulChar_add_sum q lam (geneuclidQuadChar q) a ha,
    geneuclid_mulChar_add_sum q (lam ^ 3) (geneuclidQuadChar q) a ha]
  calc
    _ ≤ ‖lam (-a) * geneuclidQuadChar q a * jacobiSum lam (geneuclidQuadChar q)‖ +
        ‖(lam ^ 3) (-a) * geneuclidQuadChar q a *
          jacobiSum (lam ^ 3) (geneuclidQuadChar q)‖ := norm_add_le _ _
    _ = Real.sqrt q + Real.sqrt q := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul,
        geneuclid_norm_mulChar_apply q lam (-a) (neg_ne_zero.mpr ha),
        geneuclid_norm_mulChar_apply q (lam ^ 3) (-a) (neg_ne_zero.mpr ha),
        geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) a ha,
        geneuclid_norm_jacobiSum q hlamNe hχNe hprod1,
        geneuclid_norm_jacobiSum q hlam3Ne hχNe hprod3]
      ring
    _ = 2 * Real.sqrt q := by ring

private theorem geneuclid_two_sqrt_lt_sub_one (q : ℕ) (hq : 13 ≤ q) :
    2 * Real.sqrt q < q - 1 := by
  have hqR : (13 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg ((q : ℝ) - 3)]

private theorem geneuclid_five_quad_two :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    let _ : NeZero 5 := ⟨by decide⟩
    (quadraticChar (ZMod 5)) (2 : ZMod 5) = -1 := by
  decide

private theorem geneuclid_five_quad_three :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    let _ : NeZero 5 := ⟨by decide⟩
    (quadraticChar (ZMod 5)) (3 : ZMod 5) = -1 := by
  decide

private theorem geneuclid_five_quad_zero :
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    let _ : NeZero 5 := ⟨by decide⟩
    (quadraticChar (ZMod 5)) (0 : ZMod 5) = 0 := by
  decide

private theorem geneuclid_five_character_witness [Fact (Nat.Prime 5)] [NeZero 5]
    (a : ZMod 5) (ha0 : a ≠ 0) (ha3 : a ≠ 3) :
    ∃ x : (ZMod 5)ˣ,
      geneuclidQuadChar 5 ((x : ZMod 5) + a / (x : ZMod 5)) ≠ 1 := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  rcases ha with h | h | h | h | h
  · exact (ha0 h).elim
  · subst a
    refine ⟨1, ?_⟩
    norm_num
    change (((quadraticChar (ZMod 5)) 2 : ℤ) : ℂ) ≠ 1
    rw [geneuclid_five_quad_two]
    norm_num
  · subst a
    refine ⟨1, ?_⟩
    norm_num
    change (((quadraticChar (ZMod 5)) 3 : ℤ) : ℂ) ≠ 1
    rw [geneuclid_five_quad_three]
    norm_num
  · exact (ha3 h).elim
  · subst a
    refine ⟨1, ?_⟩
    norm_num
    change (((quadraticChar (ZMod 5)) 0 : ℤ) : ℂ) ≠ 1
    rw [geneuclid_five_quad_zero]
    norm_num

private theorem geneuclid_character_witness_mod_four_three (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq2 : q ≠ 2) (hq4 : q % 4 = 3) (a : ZMod q) :
    ∃ x : (ZMod q)ˣ,
      geneuclidQuadChar q ((x : ZMod q) + a / (x : ZMod q)) ≠ 1 := by
  by_contra! hall
  have hpos : geneuclidQuadChar q (1 + a) = 1 := by
    simpa using hall (1 : (ZMod q)ˣ)
  have hneg : geneuclidQuadChar q (-(1 + a)) = 1 := by
    have harg : (((-1 : (ZMod q)ˣ) : ZMod q) +
        a / ((-1 : (ZMod q)ˣ) : ZMod q)) = -(1 + a) := by
      simp only [Units.val_neg, Units.val_one, div_neg, div_one]
      ring
    rw [← harg]
    exact hall (-1 : (ZMod q)ˣ)
  have hcalc : geneuclidQuadChar q (-(1 + a)) = -1 := by
    rw [show -(1 + a) = (-1 : ZMod q) * (1 + a) by ring,
      map_mul, geneuclidQuadChar_neg_one_of_mod_four_three q hq2 hq4,
      hpos]
    norm_num
  rw [hcalc] at hneg
  norm_num at hneg

private theorem geneuclid_character_witness_mod_four_one_large (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq2 : q ≠ 2) (hq4 : q % 4 = 1) (hq13 : 13 ≤ q)
    (a : ZMod q) (ha : a ≠ 0) :
    ∃ x : (ZMod q)ˣ,
      geneuclidQuadChar q ((x : ZMod q) + a / (x : ZMod q)) ≠ 1 := by
  by_contra! hall
  have hterm : ∀ x : ZMod q,
      geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a) =
        if x = 0 then 0 else 1 := by
    intro x
    by_cases hx : x = 0
    · subst x
      rw [ite_eq_left rfl, (geneuclidQuadChar q).map_zero, zero_mul]
    · rw [ite_eq_right hx]
      have hxHall := hall (Units.mk0 x hx)
      simp only [Units.val_mk0] at hxHall
      have hmul : (x + a / x) * x = x ^ 2 + a := by
        rw [add_mul, div_mul_cancel₀ a hx, pow_two]
      have hcharMul : geneuclidQuadChar q (x ^ 2 + a) =
          geneuclidQuadChar q (x + a / x) * geneuclidQuadChar q x := by
        rw [← hmul, map_mul]
      have hcharSq : geneuclidQuadChar q x ^ 2 = 1 := by
        have h := congrArg (fun χ : MulChar (ZMod q) ℂ => χ x)
          (geneuclidQuadChar_isQuadratic q).sq_eq_one
        rw [MulChar.pow_apply' (geneuclidQuadChar q) (by norm_num) x,
          MulChar.one_apply (Ne.isUnit hx)] at h
        exact h
      rw [hcharMul, hxHall, one_mul, ← pow_two, hcharSq]
  have hsum :
      (∑ x : ZMod q, geneuclidQuadChar q x * geneuclidQuadChar q (x ^ 2 + a)) =
        (q - 1 : ℕ) := by
    calc
      _ = ∑ x : ZMod q, if x = 0 then (0 : ℂ) else 1 := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hterm x
      _ = ∑ x ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          (if x = 0 then (0 : ℂ) else 1) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0)]
        simp
      _ = ∑ _x ∈ (Finset.univ : Finset (ZMod q)).erase 0, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_erase] at hx
        simp [hx.1]
      _ = (((Finset.univ : Finset (ZMod q)).erase 0).card : ℕ) := by simp
      _ = ((q - 1 : ℕ) : ℂ) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
  have hbound := geneuclid_quartic_sum_norm_le q hq2 hq4 a ha
  rw [hsum, Complex.norm_natCast,
    Nat.cast_sub (Fact.out : q.Prime).one_le, Nat.cast_one] at hbound
  linarith [geneuclid_two_sqrt_lt_sub_one q hq13]

private theorem geneuclid_character_witness (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (a : ZMod q) (ha : a ≠ 0) (hexception : q ≠ 5 ∨ a ≠ 3) :
    ∃ x : (ZMod q)ˣ,
      geneuclidQuadChar q ((x : ZMod q) + a / (x : ZMod q)) ≠ 1 := by
  have hodd : q % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : q.Prime)).mpr hq2
  rcases Nat.odd_mod_four_iff.mp hodd with hq4 | hq4
  · by_cases hq5 : q = 5
    · subst q
      have ha3 : a ≠ 3 := by
        rcases hexception with h | h
        · exact (h rfl).elim
        · exact h
      exact geneuclid_five_character_witness a ha ha3
    · have hq13 : 13 ≤ q := by
        by_contra h
        have hqle : q ≤ 12 := by omega
        have hprime : q.Prime := Fact.out
        interval_cases q <;> norm_num at hq4
        · exact (by decide : ¬Nat.Prime 1) hprime
        · exact hq5 rfl
        · exact (by decide : ¬Nat.Prime 9) hprime
      exact geneuclid_character_witness_mod_four_one_large q hq2 hq4 hq13 a ha
  · exact geneuclid_character_witness_mod_four_three q hq2 hq4 a

private theorem geneuclid_orderOf_char_generator {F : Type*} [Field F]
    {g : Fˣ} (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) (χ : MulChar F ℂ) :
    orderOf (χ.toUnitHom g) = orderOf χ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro hn
    apply (MulChar.eq_iff hg (χ ^ n) 1).mpr
    rw [MulChar.pow_apply_coe χ n g, MulChar.one_apply g.isUnit]
    exact Units.ext_iff.mp hn
  · intro hn
    apply Units.ext
    change χ (g : F) ^ n = 1
    have h := congrArg (fun ψ : MulChar F ℂ => ψ (g : F)) hn
    rw [MulChar.pow_apply_coe χ n g, MulChar.one_apply g.isUnit] at h
    exact h

private theorem geneuclid_sixth_power_range_eq_ker (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq6 : q % 6 = 1) (θ : MulChar (ZMod q) ℂ) (hθ : orderOf θ = 6) :
    (powMonoidHom 6 : (ZMod q)ˣ →* (ZMod q)ˣ).range = θ.toUnitHom.ker := by
  let C := (ZMod q)ˣ
  have hcardC : Nat.card C = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hdiv : 6 ∣ Nat.card C := by
    rw [hcardC]
    simpa [hq6] using (Nat.dvd_sub_mod (n := 6) q)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hθpow : θ ^ 6 = 1 := by
    rw [← hθ]
    exact pow_orderOf_eq_one θ
  have hle : (powMonoidHom 6 : C →* C).range ≤ θ.toUnitHom.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change θ.toUnitHom (y ^ 6) = 1
    rw [map_pow]
    apply Units.ext
    have h := congrArg (fun ψ : MulChar (ZMod q) ℂ => ψ (y : ZMod q)) hθpow
    rw [MulChar.pow_apply' θ (by norm_num) (y : ZMod q),
      MulChar.one_apply y.isUnit] at h
    exact h
  apply Subgroup.eq_of_le_of_card_ge hle
  have hgenTop : Subgroup.zpowers g = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr hg
  have hrange : θ.toUnitHom.range = Subgroup.zpowers (θ.toUnitHom g) := by
    rw [MonoidHom.range_eq_map, ← hgenTop, MonoidHom.map_zpowers]
  have hindexKer : θ.toUnitHom.ker.index = 6 := by
    calc
      _ = Nat.card θ.toUnitHom.range := Subgroup.index_ker θ.toUnitHom
      _ = Nat.card (Subgroup.zpowers (θ.toUnitHom g)) := by rw [hrange]
      _ = orderOf (θ.toUnitHom g) := Nat.card_zpowers _
      _ = orderOf θ := geneuclid_orderOf_char_generator hg θ
      _ = 6 := hθ
  have hindexRange : (powMonoidHom 6 : C →* C).range.index = 6 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdiv]
  have hcardRange := (powMonoidHom 6 : C →* C).range.card_mul_index
  have hcardKer := θ.toUnitHom.ker.card_mul_index
  rw [hindexRange] at hcardRange
  rw [hindexKer] at hcardKer
  exact (Nat.mul_right_cancel (by norm_num) (hcardRange.trans hcardKer.symm)).symm.le

private theorem geneuclid_sixth_power_fiber_sum (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq6 : q % 6 = 1) (θ : MulChar (ZMod q) ℂ) (hθ : orderOf θ = 6)
    (u : (ZMod q)ˣ) :
    (((Finset.univ.filter fun y : (ZMod q)ˣ => y ^ 6 = u).card : ℕ) : ℂ) =
      ∑ k ∈ Finset.range 6, (θ ^ k) (u : ZMod q) := by
  let C := (ZMod q)ˣ
  let f : C →* C := powMonoidHom 6
  have hcardC : Nat.card C = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hdiv : 6 ∣ Nat.card C := by
    rw [hcardC]
    simpa [hq6] using (Nat.dvd_sub_mod (n := 6) q)
  have hrangeKer : f.range = θ.toUnitHom.ker := by
    exact geneuclid_sixth_power_range_eq_ker q hq6 θ hθ
  have hrangeIff : u ∈ f.range ↔ θ (u : ZMod q) = 1 := by
    rw [hrangeKer, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  have hkerCard : Nat.card f.ker = 6 := by
    dsimp only [f]
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdiv]
  by_cases hu : u ∈ f.range
  · have hcardFibers := MonoidHom.card_fiber_eq_of_mem_range f (x := u) (y := 1)
        (⟨hu.choose, hu.choose_spec⟩ : u ∈ Set.range f) ⟨1, map_one f⟩
    have hcardOne : (Finset.univ.filter fun y : C => f y = 1).card =
        Nat.card f.ker := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      apply congrArg Finset.card
      ext y
      simp [MonoidHom.mem_ker]
    have hcard : (Finset.univ.filter fun y : C => y ^ 6 = u).card = 6 := by
      change (Finset.univ.filter fun y : C => f y = u).card = 6
      rw [hcardFibers, hcardOne, hkerCard]
    rw [hcard]
    have hθu : θ (u : ZMod q) = 1 := hrangeIff.mp hu
    simp [MulChar.pow_apply_coe, hθu]
  · have hcard : (Finset.univ.filter fun y : C => y ^ 6 = u).card = 0 := by
      rw [Finset.card_eq_zero]
      ext y
      simp only [Finset.notMem_empty, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_false]
      intro hy
      exact hu ⟨y, hy⟩
    rw [hcard, Nat.cast_zero]
    have hθu : θ (u : ZMod q) ≠ 1 := mt hrangeIff.mpr hu
    have hθpow : θ ^ 6 = 1 := by
      rw [← hθ]
      exact pow_orderOf_eq_one θ
    have huPow : θ (u : ZMod q) ^ 6 = 1 := by
      have h := congrArg (fun ψ : MulChar (ZMod q) ℂ => ψ (u : ZMod q)) hθpow
      rw [MulChar.pow_apply_coe θ 6 u, MulChar.one_apply u.isUnit] at h
      exact h
    have hgeom : ∑ k ∈ Finset.range 6, θ (u : ZMod q) ^ k = 0 := by
      have hmul := geom_sum_mul (θ (u : ZMod q)) 6
      rw [huPow, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hθu)
    simpa only [MulChar.pow_apply_coe] using hgeom.symm

private theorem geneuclid_sum_units_eq_sum {F A : Type*} [GroupWithZero F] [Fintype F]
    [DecidableEq F] [AddCommMonoid A] (f : F → A) (h0 : f 0 = 0) :
    (∑ u : Fˣ, f (u : F)) = ∑ x : F, f x := by
  calc
    _ = ∑ x : {x : F // x ≠ 0}, f (x : F) := by
      exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset F).erase 0, f x := by
      symm
      exact Finset.sum_subtype _ (by simp) f
    _ = ∑ x : F, f x := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), h0, add_zero]

private theorem geneuclid_sixth_power_sum_eq (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq6 : q % 6 = 1) (θ : MulChar (ZMod q) ℂ) (hθ : orderOf θ = 6) (a : ZMod q) :
    (∑ y : (ZMod q)ˣ, geneuclidQuadChar q ((y : ZMod q) ^ 6 + a)) =
      ∑ k ∈ Finset.range 6, ∑ u : ZMod q,
        (θ ^ k) u * geneuclidQuadChar q (u + a) := by
  let C := (ZMod q)ˣ
  calc
    _ = ∑ u : C, ∑ y ∈ Finset.univ with y ^ 6 = u,
        geneuclidQuadChar q ((y : ZMod q) ^ 6 + a) := by
      symm
      simpa only using
        (Finset.sum_fiberwise Finset.univ (fun y : C => y ^ 6)
          (fun y => geneuclidQuadChar q ((y : ZMod q) ^ 6 + a)))
    _ = ∑ u : C,
        (((Finset.univ.filter fun y : C => y ^ 6 = u).card : ℕ) : ℂ) *
          geneuclidQuadChar q ((u : ZMod q) + a) := by
      apply Finset.sum_congr rfl
      intro u _hu
      calc
        _ = ∑ _y ∈ Finset.univ.filter (fun y : C => y ^ 6 = u),
            geneuclidQuadChar q ((u : ZMod q) + a) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mem_filter] at hy
          rw [← hy.2]
          rw [Units.val_pow_eq_pow_val]
        _ = (((Finset.univ.filter fun y : C => y ^ 6 = u).card : ℕ) : ℂ) *
            geneuclidQuadChar q ((u : ZMod q) + a) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ u : C, (∑ k ∈ Finset.range 6, (θ ^ k) (u : ZMod q)) *
          geneuclidQuadChar q ((u : ZMod q) + a) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [geneuclid_sixth_power_fiber_sum q hq6 θ hθ u]
    _ = ∑ u : C, ∑ k ∈ Finset.range 6,
          (θ ^ k) (u : ZMod q) * geneuclidQuadChar q ((u : ZMod q) + a) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.range 6, ∑ u : C,
          (θ ^ k) (u : ZMod q) * geneuclidQuadChar q ((u : ZMod q) + a) := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range 6, ∑ u : ZMod q,
          (θ ^ k) u * geneuclidQuadChar q (u + a) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact geneuclid_sum_units_eq_sum
        (fun u : ZMod q => (θ ^ k) u * geneuclidQuadChar q (u + a))
        (by rw [(θ ^ k).map_zero, zero_mul])

private theorem geneuclid_sextic_cube_eq_quad (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (θ : MulChar (ZMod q) ℂ) (hθ : orderOf θ = 6) :
    θ ^ 3 = geneuclidQuadChar q := by
  have hθsix : θ ^ 6 = 1 := by
    rw [← hθ]
    exact pow_orderOf_eq_one θ
  have hθcubeSq : (θ ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hθsix
  have hθcubeNe : θ ^ 3 ≠ 1 := by
    intro h
    have hdvd : 6 ∣ 3 := by
      rw [← hθ]
      exact orderOf_dvd_of_pow_eq_one h
    norm_num at hdvd
  exact geneuclid_quadratic_mulChar_unique hθcubeSq
    (geneuclidQuadChar_isQuadratic q).sq_eq_one hθcubeNe
    (geneuclidQuadChar_ne_one q hq2)

private theorem geneuclid_regular_shifted_sum_norm (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (ψ : MulChar (ZMod q) ℂ) (hψ : ψ ≠ 1)
    (hprod : ψ * geneuclidQuadChar q ≠ 1) (a : ZMod q) (ha : a ≠ 0) :
    ‖∑ u : ZMod q, ψ u * geneuclidQuadChar q (u + a)‖ = Real.sqrt q := by
  rw [geneuclid_mulChar_add_sum q ψ (geneuclidQuadChar q) a ha,
    norm_mul, norm_mul,
    geneuclid_norm_mulChar_apply q ψ (-a) (neg_ne_zero.mpr ha),
    geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) a ha,
    geneuclid_norm_jacobiSum q hψ (geneuclidQuadChar_ne_one q hq2) hprod]
  ring

private theorem geneuclid_trivial_shifted_sum_norm (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (a : ZMod q) (ha : a ≠ 0) :
    ‖∑ u : ZMod q, (1 : MulChar (ZMod q) ℂ) u * geneuclidQuadChar q (u + a)‖ = 1 := by
  rw [geneuclid_mulChar_add_sum q 1 (geneuclidQuadChar q) a ha,
    jacobiSum_one_nontrivial (geneuclidQuadChar_ne_one q hq2),
    norm_mul, norm_mul,
    geneuclid_norm_mulChar_apply q (1 : MulChar (ZMod q) ℂ) (-a) (neg_ne_zero.mpr ha),
    geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) a ha, norm_neg, norm_one]
  ring

private theorem geneuclid_quadratic_shifted_sum_norm (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq2 : q ≠ 2) (a : ZMod q) (ha : a ≠ 0) :
    ‖∑ u : ZMod q, geneuclidQuadChar q u * geneuclidQuadChar q (u + a)‖ = 1 := by
  have hχNe := geneuclidQuadChar_ne_one q hq2
  have hj := jacobiSum_nontrivial_inv hχNe
  rw [(geneuclidQuadChar_isQuadratic q).inv] at hj
  rw [geneuclid_mulChar_add_sum q (geneuclidQuadChar q) (geneuclidQuadChar q) a ha,
    hj, norm_mul, norm_mul,
    geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) (-a) (neg_ne_zero.mpr ha),
    geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) a ha, norm_neg,
    geneuclid_norm_mulChar_apply q (geneuclidQuadChar q) (-1) (by norm_num)]
  ring

private theorem geneuclid_sextic_term_norm_le (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (θ : MulChar (ZMod q) ℂ) (hθ : orderOf θ = 6)
    (a : ZMod q) (ha : a ≠ 0) (k : ℕ) (hk : k < 6) :
    ‖∑ u : ZMod q, (θ ^ k) u * geneuclidQuadChar q (u + a)‖ ≤
      if k = 0 ∨ k = 3 then 1 else Real.sqrt q := by
  have hpowNe (m : ℕ) (hm : ¬6 ∣ m) : θ ^ m ≠ 1 := by
    intro h
    apply hm
    rw [← hθ]
    exact orderOf_dvd_of_pow_eq_one h
  have hcube : θ ^ 3 = geneuclidQuadChar q :=
    geneuclid_sextic_cube_eq_quad q hq2 θ hθ
  have hprodNe (m : ℕ) (hm : ¬6 ∣ m + 3) :
      θ ^ m * geneuclidQuadChar q ≠ 1 := by
    rw [← hcube, ← pow_add]
    exact hpowNe (m + 3) hm
  interval_cases k
  · simpa using (geneuclid_trivial_shifted_sum_norm q hq2 a ha).le
  · simpa using (geneuclid_regular_shifted_sum_norm q hq2 θ
      (by simpa only [pow_one] using hpowNe 1 (by norm_num))
      (by simpa only [pow_one] using hprodNe 1 (by norm_num)) a ha).le
  · simpa using (geneuclid_regular_shifted_sum_norm q hq2 (θ ^ 2)
      (hpowNe 2 (by norm_num)) (hprodNe 2 (by norm_num)) a ha).le
  · simpa [hcube] using (geneuclid_quadratic_shifted_sum_norm q hq2 a ha).le
  · simpa using (geneuclid_regular_shifted_sum_norm q hq2 (θ ^ 4)
      (hpowNe 4 (by norm_num)) (hprodNe 4 (by norm_num)) a ha).le
  · simpa using (geneuclid_regular_shifted_sum_norm q hq2 (θ ^ 5)
      (hpowNe 5 (by norm_num)) (hprodNe 5 (by norm_num)) a ha).le

private theorem geneuclid_sixth_power_sum_norm_le (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (hq6 : q % 6 = 1) (a : ZMod q) (ha : a ≠ 0) :
    ‖∑ y : (ZMod q)ˣ, geneuclidQuadChar q ((y : ZMod q) ^ 6 + a)‖ ≤
      2 + 4 * Real.sqrt q := by
  have hdiv : 6 ∣ Fintype.card (ZMod q) - 1 := by
    rw [ZMod.card]
    simpa [hq6] using (Nat.dvd_sub_mod (n := 6) q)
  obtain ⟨θ, hθ⟩ := MulChar.exists_mulChar_orderOf (ZMod q) hdiv
    (Complex.isPrimitiveRoot_exp 6 (by norm_num))
  rw [geneuclid_sixth_power_sum_eq q hq6 θ hθ a]
  calc
    _ ≤ ∑ k ∈ Finset.range 6,
        ‖∑ u : ZMod q, (θ ^ k) u * geneuclidQuadChar q (u + a)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range 6,
        if k = 0 ∨ k = 3 then 1 else Real.sqrt q := by
      apply Finset.sum_le_sum
      intro k hk
      exact geneuclid_sextic_term_norm_le q hq2 θ hθ a ha k (Finset.mem_range.mp hk)
    _ = 2 + 4 * Real.sqrt q := by
      norm_num [Finset.sum_range_succ]
      ring

private theorem geneuclid_four_sqrt_lt_sub_three (q : ℕ) (hq : 31 ≤ q) :
    2 + 4 * Real.sqrt q < q - 1 := by
  have hqR : (31 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (Real.sqrt (q : ℝ) - 4)]

private theorem geneuclid_nineteen_witness_decision :
    let _ : Fact (Nat.Prime 19) := ⟨by decide⟩
    let _ : NeZero 19 := ⟨by decide⟩
    ∀ a : ZMod 19, a ≠ 0 → ∃ y : ZMod 19,
      y ≠ 0 ∧ (quadraticChar (ZMod 19)) (y ^ 6 + a) ≠ 1 := by
  decide

private theorem geneuclid_nineteen_character_witness [Fact (Nat.Prime 19)] [NeZero 19]
    (a : ZMod 19) (ha : a ≠ 0) :
    ∃ y : (ZMod 19)ˣ, geneuclidQuadChar 19 ((y : ZMod 19) ^ 6 + a) ≠ 1 := by
  obtain ⟨y, hy0, hy⟩ := geneuclid_nineteen_witness_decision a ha
  refine ⟨Units.mk0 y hy0, ?_⟩
  simp only [Units.val_mk0]
  change (((quadraticChar (ZMod 19)) (y ^ 6 + a) : ℤ) : ℂ) ≠ 1
  intro h
  apply hy
  exact_mod_cast h

private theorem geneuclid_sixth_power_character_witness (q : ℕ) [Fact q.Prime]
    [NeZero q] (hq6 : q % 6 = 1) (hq7 : q ≠ 7) (hq13 : q ≠ 13)
    (a : ZMod q) (ha : a ≠ 0) :
    ∃ y : (ZMod q)ˣ, geneuclidQuadChar q ((y : ZMod q) ^ 6 + a) ≠ 1 := by
  have hq2 : q ≠ 2 := by omega
  by_cases hq19 : q = 19
  · subst q
    exact geneuclid_nineteen_character_witness a ha
  · have hq31 : 31 ≤ q := by
      by_contra h
      have hqle : q ≤ 30 := by omega
      have hprime : q.Prime := Fact.out
      interval_cases q <;> norm_num at hq6
      · exact (by decide : ¬Nat.Prime 1) hprime
      · exact hq7 rfl
      · exact hq13 rfl
      · exact hq19 rfl
      · exact (by decide : ¬Nat.Prime 25) hprime
    by_contra! hall
    have hsum :
        (∑ y : (ZMod q)ˣ, geneuclidQuadChar q ((y : ZMod q) ^ 6 + a)) =
          ((q - 1 : ℕ) : ℂ) := by
      calc
        _ = ∑ _y : (ZMod q)ˣ, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact hall y
        _ = (Fintype.card (ZMod q)ˣ : ℕ) := by simp
        _ = ((q - 1 : ℕ) : ℂ) := by rw [Fintype.card_units, ZMod.card]
    have hbound := geneuclid_sixth_power_sum_norm_le q hq2 hq6 a ha
    rw [hsum, Complex.norm_natCast,
      Nat.cast_sub (Fact.out : q.Prime).one_le, Nat.cast_one] at hbound
    linarith [geneuclid_four_sqrt_lt_sub_three q hq31]

private theorem geneuclid_exists_prime_factor_map_ne_one {M : Type*} [CommMonoid M]
    (f : ℕ → M) (fone : f 1 = 1) (fmul : ∀ a b, f (a * b) = f a * f b)
    {m : ℕ} (hm0 : m ≠ 0) (hm : f m ≠ 1) :
    ∃ p, p.Prime ∧ p ∣ m ∧ f p ≠ 1 := by
  by_contra h
  push Not at h
  have hfac : ∀ p ∈ m.primeFactorsList, p.Prime ∧ p ∣ m := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp⟩
  have hprod : ∀ L : List ℕ, (∀ p ∈ L, p.Prime ∧ p ∣ m) → f L.prod = 1 := by
    intro L hL
    induction L with
    | nil => simpa using fone
    | cons p L ih =>
      rw [List.prod_cons, fmul, h p (hL p (by simp)).1 (hL p (by simp)).2,
        ih (fun r hr => hL r (by simp [hr]))]
      simp
  apply hm
  rw [← Nat.prod_primeFactorsList hm0]
  exact hprod _ hfac

private theorem geneuclidQuadChar_eq_neg_one_of_ne_one (q : ℕ) [Fact q.Prime]
    [NeZero q] {a : ZMod q} (ha : a ≠ 0) (hne : geneuclidQuadChar q a ≠ 1) :
    geneuclidQuadChar q a = -1 := by
  change (((quadraticChar (ZMod q)) a : ℤ) : ℂ) = -1
  change (((quadraticChar (ZMod q)) a : ℤ) : ℂ) ≠ 1 at hne
  rcases quadraticChar_dichotomy ha with h | h
  · exact (hne (by exact_mod_cast h)).elim
  · exact_mod_cast h

private theorem geneuclidProduct_ne_zero_mod (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l) :
    (geneuclidProduct l : ZMod q) ≠ 0 := by
  apply geneuclidResidues_ne_zero l hprime q Fact.out hqnot
  apply (mem_geneuclidResidues_iff q l _).mpr
  refine ⟨Finset.range l.length, Finset.Subset.rfl, ?_⟩
  simp [geneuclidProduct]

private theorem geneuclid_nat_unit_mem_subgroup (q : ℕ) [Fact q.Prime] [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (m : ℕ) (hmq : ¬q ∣ m)
    (hprime : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), p.Prime → p ∣ m →
      Units.mk0 (p : ZMod q) hp0 ∈ H) :
    Units.mk0 (m : ZMod q) (mt (ZMod.natCast_eq_zero_iff m q).mp hmq) ∈ H := by
  induction m using induction_on_primes with
  | zero => exact (hmq (dvd_zero q)).elim
  | one => simp [H.one_mem]
  | prime_mul p a hp ih =>
      have hqp : ¬q ∣ p := fun h => hmq (dvd_mul_of_dvd_left h a)
      have hqa : ¬q ∣ a := fun h => hmq (dvd_mul_of_dvd_right h p)
      have hp0 : (p : ZMod q) ≠ 0 := mt (ZMod.natCast_eq_zero_iff p q).mp hqp
      have ha0 : (a : ZMod q) ≠ 0 := mt (ZMod.natCast_eq_zero_iff a q).mp hqa
      have hpmem : Units.mk0 (p : ZMod q) hp0 ∈ H := by
        apply hprime p hp0 hp
        exact dvd_mul_right p a
      have hamem : Units.mk0 (a : ZMod q) ha0 ∈ H := by
        apply ih hqa
        intro r hr0 hr hrdvd
        apply hprime r hr0 hr
        exact dvd_mul_of_dvd_right hrdvd p
      convert H.mul_mem hpmem hamem using 1
      ext
      simp

private theorem geneuclid_expression_fiber_card_le_two (q : ℕ) [Fact q.Prime]
    [NeZero q] (n : ZMod q) (hn : n ≠ 0) (s : Finset (ZMod q)ˣ) (b : ZMod q) :
    (s.filter fun (u : (ZMod q)ˣ) => (u : ZMod q) + n / (u : ZMod q) = b).card ≤ 2 := by
  let fiber : Finset (ZMod q)ˣ :=
    s.filter fun (u : (ZMod q)ˣ) => (u : ZMod q) + n / (u : ZMod q) = b
  change fiber.card ≤ 2
  by_cases hempty : fiber.Nonempty
  · obtain ⟨x, hx⟩ := hempty
    let c : (ZMod q)ˣ := Units.mk0 n hn * x⁻¹
    have hsub : fiber ⊆ {x, c} := by
      intro y hy
      have hxeq := (Finset.mem_filter.mp hx).2
      have hyeq := (Finset.mem_filter.mp hy).2
      have heq : (x : ZMod q) + n / (x : ZMod q) =
          (y : ZMod q) + n / (y : ZMod q) := hxeq.trans hyeq.symm
      have hfactor : ((x : ZMod q) - (y : ZMod q)) *
          ((x : ZMod q) * (y : ZMod q) - n) = 0 := by
        field_simp at heq
        linear_combination heq
      rcases mul_eq_zero.mp hfactor with hxy | hxy
      · rw [Finset.mem_insert]
        left
        exact Units.ext (sub_eq_zero.mp hxy).symm
      · rw [Finset.mem_insert, Finset.mem_singleton]
        right
        apply Units.ext
        simp only [c, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        field_simp
        simpa [mul_comm] using sub_eq_zero.mp hxy
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [fiber, hempty]

private theorem geneuclid_expression_unit_mem_stabilizer (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l))
    (u : (ZMod q)ˣ) (hu : u ∈ geneuclidUnits q l) :
    ∃ hz : (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) ≠ 0,
      Units.mk0 ((u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q)) hz ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l) := by
  obtain ⟨I, hI, hExpr⟩ := geneuclid_unit_expression q l u hu
  have hmq : ¬q ∣ geneuclidN l I := fun hdiv =>
    hqnotapp ⟨Fact.out, I, hI, hdiv⟩
  have hm0 : ((geneuclidN l I : ℕ) : ZMod q) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mp hmq
  have hmem := geneuclid_nat_unit_mem_subgroup q
    (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)) (geneuclidN l I) hmq
    (fun p hp0 hpprime hpdvd => hstable p hp0 ⟨hpprime, I, hI, hpdvd⟩)
  have hz : (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) ≠ 0 := by
    rw [hExpr]
    exact hm0
  refine ⟨hz, ?_⟩
  convert hmem using 1
  ext
  exact hExpr

private theorem geneuclid_stable_card_bound (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l)
    (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)) :
    (geneuclidUnits q l).card ≤ 2 *
      Nat.card (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)) := by
  let S := geneuclidUnits q l
  let H := MulAction.stabilizer (ZMod q)ˣ S
  let _ : Fintype H := Fintype.ofFinite H
  let n : ZMod q := geneuclidProduct l
  let f : (ZMod q)ˣ → ZMod q := fun u => (u : ZMod q) + n / (u : ZMod q)
  let image := S.image f
  let Hvals := Finset.univ.image fun u : H => ((u : (ZMod q)ˣ) : ZMod q)
  have hn0 : n ≠ 0 := geneuclidProduct_ne_zero_mod q l hprime hqnot
  have htwo : S.card ≤ 2 * image.card := by
    apply Finset.card_le_mul_card_image S 2
    intro b _hb
    simpa [f, n] using geneuclid_expression_fiber_card_le_two q n hn0 S b
  have hsubset : image ⊆ Hvals := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hz, hmem⟩ := geneuclid_expression_unit_mem_stabilizer q l hqnotapp
      hstable u hu
    apply Finset.mem_image.mpr
    refine ⟨⟨Units.mk0 (f u) ?_, ?_⟩, Finset.mem_univ _, rfl⟩
    · simpa [f, n] using hz
    · simpa [H, S, f, n] using hmem
  have himage : image.card ≤ Hvals.card := Finset.card_le_card hsubset
  have hHvals : Hvals.card = Nat.card H := by
    rw [Finset.card_image_of_injective]
    · exact Nat.card_eq_fintype_card.symm
    · intro a b hab
      exact Subtype.ext (Units.ext hab)
  change S.card ≤ 2 * Nat.card H
  omega

private theorem geneuclid_two_cosets_le {G : Type*} [CommGroup G] [Finite G]
    (H : Subgroup G) (S : Finset G)
    (hstable : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S) (hone : 1 ∈ S)
    {s : G} (hs : s ∈ S) (hsH : s ∉ H) :
    2 * Nat.card H ≤ S.card := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype H := Fintype.ofFinite H
  let f : H ⊕ H → {x // x ∈ S}
    | Sum.inl h => ⟨h, by simpa using hstable h h.2 1 hone⟩
    | Sum.inr h => ⟨h * s, hstable h h.2 s hs⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with h | h <;> rcases b with k | k
    · apply congrArg Sum.inl
      apply Subtype.ext
      have heq := congrArg Subtype.val hab
      simpa [f] using heq
    · exfalso
      apply hsH
      have heq : (h : G) = (k : G) * s := by
        have heq := congrArg Subtype.val hab
        simpa [f] using heq
      have hsEq : s = (k : G)⁻¹ * (h : G) := by
        rw [heq]
        simp
      rw [hsEq]
      exact H.mul_mem (H.inv_mem k.2) h.2
    · exfalso
      apply hsH
      have heq : (h : G) * s = (k : G) := by
        have heq := congrArg Subtype.val hab
        simpa [f] using heq
      have hsEq : s = (h : G)⁻¹ * (k : G) := by
        rw [← heq]
        simp
      rw [hsEq]
      exact H.mul_mem (H.inv_mem h.2) k.2
    · apply congrArg Sum.inr
      apply Subtype.ext
      have heq := congrArg Subtype.val hab
      have heq' : (h : G) * s = (k : G) * s := by simpa [f] using heq
      exact mul_right_cancel heq'
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sum, Fintype.card_coe S, ← Nat.card_eq_fintype_card] at hcard
  omega

private theorem geneuclid_exists_mem_not_subgroup {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (S : Finset G) (hcard : Nat.card H < S.card) :
    ∃ s ∈ S, s ∉ H := by
  by_contra h
  push Not at h
  let _ : Fintype H := Fintype.ofFinite H
  let f : {x // x ∈ S} → H := fun x => ⟨x, h x x.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have heq := congrArg Subtype.val hab
    simpa [f] using heq
  have hle := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe S, ← Nat.card_eq_fintype_card] at hle
  omega

private theorem geneuclid_fiber_card_eq_two {A B : Type*} [DecidableEq B]
    (s : Finset A) (t : Finset B) (f : A → B)
    (hmap : Set.MapsTo f (s : Set A) (t : Set B))
    (hcard : s.card = 2 * t.card)
    (hbound : ∀ b ∈ t, (s.filter fun a => f a = b).card ≤ 2) :
    ∀ b ∈ t, (s.filter fun a => f a = b).card = 2 := by
  intro b hb
  have hle := hbound b hb
  by_contra hne
  have hleone : (s.filter fun a => f a = b).card ≤ 1 := by omega
  let fibers : B → ℕ := fun c => (s.filter fun a => f a = c).card
  have hsum : s.card = ∑ c ∈ t, fibers c := by
    simpa [fibers] using Finset.card_eq_sum_card_fiberwise hmap
  have herase : ∑ c ∈ t.erase b, fibers c ≤ (t.erase b).card * 2 := by
    simpa using Finset.sum_le_card_nsmul (t.erase b) fibers 2
      (fun c hc => hbound c (Finset.mem_of_mem_erase hc))
  have hsplit := Finset.sum_erase_add t fibers hb
  have herasecard := Finset.card_erase_of_mem hb
  have htpos : 0 < t.card := Finset.card_pos.mpr ⟨b, hb⟩
  change fibers b ≤ 1 at hleone
  omega

private theorem geneuclid_index_three_card_data (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l)
    (hmin : ∀ p, p.Prime → p < q → p ∈ l)
    (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l))
    (hindex : (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)).index = 3) :
    (geneuclidUnits q l).card = 2 *
        Nat.card (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)) ∧
      q ≠ 7 ∧ q ≠ 13 := by
  let S := geneuclidUnits q l
  let H := MulAction.stabilizer (ZMod q)ˣ S
  have hCcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hgroup := H.card_mul_index
  rw [hCcard, hindex] at hgroup
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hlarge : q - 1 < 2 * S.card := geneuclidUnits_large q hq2 l hmin
  have hbound : S.card ≤ 2 * Nat.card H :=
    geneuclid_stable_card_bound q l hprime hqnot hqnotapp hstable
  have hHstable : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S := by
    intro h hh x hx
    have hm := (MulAction.mem_stabilizer_finset').mp hh hx
    simpa [smul_eq_mul] using hm
  have hone : (1 : (ZMod q)ˣ) ∈ S := by
    rw [mem_geneuclidUnits_iff]
    apply (mem_geneuclidResidues_iff q l _).mpr
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  have hSH : Nat.card H < S.card := by omega
  obtain ⟨s, hs, hsH⟩ := geneuclid_exists_mem_not_subgroup H S hSH
  have hlower : 2 * Nat.card H ≤ S.card :=
    geneuclid_two_cosets_le H S hHstable hone hs hsH
  have hcard : S.card = 2 * Nat.card H := by omega
  have hq7 : q ≠ 7 := by
    intro hq
    subst q
    have hrep : 5 ≤ S.card := by
      rw [← geneuclidSevenRepresentatives_card]
      apply Finset.card_le_card
      exact geneuclidSevenRepresentatives_subset l hmin
    omega
  have hq13 : q ≠ 13 := by
    intro hq
    subst q
    have hrep : 12 ≤ S.card := by
      rw [← geneuclidThirteenRepresentatives_card]
      apply Finset.card_le_card
      exact geneuclidThirteenRepresentatives_subset l hmin
    omega
  exact ⟨hcard, hq7, hq13⟩

private theorem geneuclid_stable_discriminant_is_square (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l)
    (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l))
    (hcard : (geneuclidUnits q l).card = 2 *
      Nat.card (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l))) :
    ∀ h ∈ MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l),
      geneuclidQuadChar q ((h : ZMod q) ^ 2 - 4 * (geneuclidProduct l : ZMod q)) = 1 := by
  let S := geneuclidUnits q l
  let H := MulAction.stabilizer (ZMod q)ˣ S
  let _ : Fintype H := Fintype.ofFinite H
  let n : ZMod q := geneuclidProduct l
  let f : (ZMod q)ˣ → ZMod q := fun u => (u : ZMod q) + n / (u : ZMod q)
  let T := Finset.univ.image fun h : H => ((h : (ZMod q)ˣ) : ZMod q)
  have hn0 : n ≠ 0 := geneuclidProduct_ne_zero_mod q l hprime hqnot
  have hTcard : T.card = Nat.card H := by
    rw [Finset.card_image_of_injective]
    · exact Nat.card_eq_fintype_card.symm
    · intro a b hab
      exact Subtype.ext (Units.ext hab)
  have hmap : Set.MapsTo f (S : Set (ZMod q)ˣ) (T : Set (ZMod q)) := by
    intro u hu
    obtain ⟨hz, hmem⟩ := geneuclid_expression_unit_mem_stabilizer q l hqnotapp
      hstable u hu
    apply Finset.mem_image.mpr
    refine ⟨⟨Units.mk0 (f u) ?_, ?_⟩, Finset.mem_univ _, rfl⟩
    · simpa [f, n] using hz
    · simpa [H, S, f, n] using hmem
  have hcard' : S.card = 2 * T.card := by
    rw [hTcard]
    exact hcard
  have hfiber : ∀ b ∈ T, (S.filter fun u => f u = b).card = 2 := by
    apply geneuclid_fiber_card_eq_two S T f hmap hcard'
    intro b _hb
    simpa [f, n] using geneuclid_expression_fiber_card_le_two q n hn0 S b
  intro h hh
  let hH : H := ⟨h, hh⟩
  have hb : (h : ZMod q) ∈ T := by
    apply Finset.mem_image.mpr
    exact ⟨hH, Finset.mem_univ _, rfl⟩
  have hfib := hfiber (h : ZMod q) hb
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hfib
  have hxmem : x ∈ S ∧ f x = (h : ZMod q) := by
    exact Finset.mem_filter.mp (hset.symm ▸ Finset.mem_insert_self x {y})
  have hymem : y ∈ S ∧ f y = (h : ZMod q) := by
    exact Finset.mem_filter.mp (hset.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  have heq : (x : ZMod q) + n / (x : ZMod q) =
      (y : ZMod q) + n / (y : ZMod q) := by
    simpa [f] using hxmem.2.trans hymem.2.symm
  have hfactor : ((x : ZMod q) - (y : ZMod q)) *
      ((x : ZMod q) * (y : ZMod q) - n) = 0 := by
    field_simp at heq
    linear_combination heq
  have hdiff : (x : ZMod q) - (y : ZMod q) ≠ 0 := by
    rw [sub_ne_zero]
    intro hval
    exact hxy (Units.ext hval)
  have hprod : (x : ZMod q) * (y : ZMod q) = n := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hdiff)
  have hxEq : (x : ZMod q) + n / (x : ZMod q) = (h : ZMod q) := by
    simpa [f] using hxmem.2
  have hsum : (x : ZMod q) + (y : ZMod q) = (h : ZMod q) := by
    field_simp at hxEq
    apply mul_left_cancel₀ x.ne_zero
    rw [mul_add, hprod, ← pow_two]
    exact hxEq
  have hdisc : (h : ZMod q) ^ 2 - 4 * n =
      ((x : ZMod q) - (y : ZMod q)) ^ 2 := by
    rw [← hprod, ← hsum]
    ring
  change (((quadraticChar (ZMod q)) ((h : ZMod q) ^ 2 - 4 * n) : ℤ) : ℂ) = 1
  rw [hdisc]
  exact_mod_cast quadraticChar_sq_one' hdiff

private theorem geneuclid_index_three_impossible (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l)
    (hmin : ∀ p, p.Prime → p < q → p ∈ l)
    (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l))
    (hindex : (MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)).index = 3) :
    False := by
  let S := geneuclidUnits q l
  let H := MulAction.stabilizer (ZMod q)ˣ S
  obtain ⟨hcard, hq7, hq13⟩ := geneuclid_index_three_card_data q hq2 l hprime
    hqnot hmin hqnotapp hstable hindex
  have hdisc := geneuclid_stable_discriminant_is_square q l hprime hqnot hqnotapp
    hstable hcard
  have hCcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hgroup := H.card_mul_index
  rw [hCcard, hindex] at hgroup
  have hq3 : 3 ≤ q := by
    have := (Fact.out : q.Prime).two_le
    omega
  have hqodd : q % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : q.Prime)).mpr hq2
  have hq6 : q % 6 = 1 := by omega
  let n : ZMod q := geneuclidProduct l
  have hn0 : n ≠ 0 := geneuclidProduct_ne_zero_mod q l hprime hqnot
  have hfour : (4 : ZMod q) ≠ 0 := by
    intro hzero
    have hqd : q ∣ 4 := (ZMod.natCast_eq_zero_iff 4 q).mp hzero
    have hqpow : q ∣ 2 ^ 2 := by norm_num at hqd ⊢; exact hqd
    have hqd2 : q ∣ 2 := (Fact.out : q.Prime).dvd_of_dvd_pow hqpow
    exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp hqd2)
  have ha : (-4 * n : ZMod q) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hfour) hn0
  obtain ⟨y, hy⟩ := geneuclid_sixth_power_character_witness q hq6 hq7 hq13
    (-4 * n) ha
  have hyH : y ^ 3 ∈ H := by
    rw [← hindex]
    exact H.pow_index_mem y
  have hone := hdisc (y ^ 3) hyH
  apply hy
  have heq : (y : ZMod q) ^ 6 + (-4 * n) =
      ((y ^ 3 : (ZMod q)ˣ) : ZMod q) ^ 2 - 4 * n := by
    rw [Units.val_pow_eq_pow_val]
    ring
  rw [heq]
  exact hone

private theorem geneuclid_stable_units_eq_univ (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l)
    (hmin : ∀ p, p.Prime → p < q → p ∈ l)
    (hqnotapp : ¬GeneuclidAppendable l q)
    (hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0), GeneuclidAppendable l p →
      Units.mk0 (p : ZMod q) hp0 ∈
        MulAction.stabilizer (ZMod q)ˣ (geneuclidUnits q l)) :
    geneuclidUnits q l = Finset.univ := by
  let S := geneuclidUnits q l
  let H := MulAction.stabilizer (ZMod q)ˣ S
  have hCcard : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  have hgroup := H.card_mul_index
  rw [hCcard] at hgroup
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hlarge : q - 1 < 2 * S.card := geneuclidUnits_large q hq2 l hmin
  have hbound : S.card ≤ 2 * Nat.card H :=
    geneuclid_stable_card_bound q l hprime hqnot hqnotapp hstable
  have hindexlt : H.index < 4 := by
    apply (Nat.mul_lt_mul_left hHpos).mp
    calc
      Nat.card H * H.index = q - 1 := hgroup
      _ < 2 * S.card := hlarge
      _ ≤ 2 * (2 * Nat.card H) := Nat.mul_le_mul_left 2 hbound
      _ = Nat.card H * 4 := by ring
  have hindexpos : 0 < H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
  have hcases : H.index = 1 ∨ H.index = 2 ∨ H.index = 3 := by omega
  have hHstable : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S := by
    intro h hh x hx
    have hm := (MulAction.mem_stabilizer_finset').mp hh hx
    simpa [smul_eq_mul] using hm
  have hone : (1 : (ZMod q)ˣ) ∈ S := by
    rw [mem_geneuclidUnits_iff]
    apply (mem_geneuclidResidues_iff q l _).mpr
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  rcases hcases with hindex | hindex | hindex
  · have htop : H = ⊤ := Subgroup.index_eq_one.mp hindex
    apply Finset.eq_univ_of_forall
    intro u
    have hu := hHstable u (by rw [htop]; simp) 1 hone
    simpa using hu
  · have hgroup' : 2 * Nat.card H = q - 1 := by
      have hgroup' : Nat.card H * 2 = q - 1 := by simpa [hindex] using hgroup
      omega
    have hSH : Nat.card H < S.card := by omega
    obtain ⟨s, hs, hsH⟩ := geneuclid_exists_mem_not_subgroup H S hSH
    have hlower : 2 * Nat.card H ≤ S.card :=
      geneuclid_two_cosets_le H S hHstable hone hs hsH
    have htotal : S.card ≤ q - 1 := by
      have hle := Finset.card_le_univ S
      rwa [Fintype.card_units, ZMod.card] at hle
    have hScard : S.card = q - 1 := by omega
    apply Finset.eq_univ_of_card
    rw [Fintype.card_units, ZMod.card]
    exact hScard
  · exact (geneuclid_index_three_impossible q hq2 l hprime hqnot hmin hqnotapp
      hstable hindex).elim

private theorem fresh_of_dvd_euclid (l : List ℕ) (hnod : l.Nodup)
    (hprime : ∀ x ∈ l, x.Prime) (I : Finset ℕ) (hI : I ⊆ Finset.range l.length)
    (q : ℕ) (hq : q.Prime)
    (hdvd : q ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i) :
    q ∉ l := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, hjq⟩ := hmem
  have hjprime : (l[j]).Prime := hprime l[j] (List.getElem_mem hj)
  have hqj : q = l[j] := hjq.symm
  have heq : eVal l j = l[j] := eVal_lt l j hj
  by_cases hjI : j ∈ I
  · have hdvdI : q ∣ ∏ i ∈ I, eVal l i := by
      have h1 := Finset.dvd_prod_of_mem (fun i => eVal l i) hjI
      rwa [heq, ← hqj] at h1
    have hdvdC : q ∣ ∏ i ∈ (Finset.range l.length \ I), eVal l i := by
      have h := Nat.dvd_sub hdvd hdvdI
      rwa [Nat.add_sub_cancel_left] at h
    rw [hq.prime.dvd_finsetProd_iff] at hdvdC
    obtain ⟨i, hiC, hqi⟩ := hdvdC
    rw [Finset.mem_sdiff, Finset.mem_range] at hiC
    obtain ⟨hilt, hiI⟩ := hiC
    have hiprime : (l[i]).Prime := hprime l[i] (List.getElem_mem hilt)
    have heqi : eVal l i = l[i] := eVal_lt l i hilt
    have hji : l[j] = l[i] := by
      rw [hqj, heqi] at hqi
      exact (Nat.prime_dvd_prime_iff_eq hjprime hiprime).mp hqi
    have hne : j ≠ i := fun h => hiI (h ▸ hjI)
    exact hne ((List.Nodup.getElem_inj_iff hnod).mp hji)
  · have hjC : j ∈ Finset.range l.length \ I := by
      rw [Finset.mem_sdiff, Finset.mem_range]
      exact ⟨hj, hjI⟩
    have hdvdC : q ∣ ∏ i ∈ (Finset.range l.length \ I), eVal l i := by
      have h1 := Finset.dvd_prod_of_mem (fun i => eVal l i) hjC
      rwa [heq, ← hqj] at h1
    have hdvdI : q ∣ ∏ i ∈ I, eVal l i := by
      have h := Nat.dvd_sub hdvd hdvdC
      rw [Nat.add_sub_cancel] at h
      exact h
    rw [hq.prime.dvd_finsetProd_iff] at hdvdI
    obtain ⟨i, hiI, hqi⟩ := hdvdI
    have hilt : i < l.length := by
      have := hI hiI
      rw [Finset.mem_range] at this
      exact this
    have hiprime : (l[i]).Prime := hprime l[i] (List.getElem_mem hilt)
    have heqi : eVal l i = l[i] := eVal_lt l i hilt
    have hji : l[j] = l[i] := by
      rw [hqj, heqi] at hqi
      exact (Nat.prime_dvd_prime_iff_eq hjprime hiprime).mp hqi
    have hne : j ≠ i := fun h => hjI (h ▸ hiI)
    exact hne ((List.Nodup.getElem_inj_iff hnod).mp hji)

/-- Every entry of a prime list is at least `1`. -/
private theorem eVal_ge_one (l : List ℕ) (hprime : ∀ x ∈ l, x.Prime) (i : ℕ)
    (hi : i < l.length) : 1 ≤ eVal l i := by
  rw [eVal_lt l i hi]
  exact (hprime l[i] (List.getElem_mem hi)).one_lt.le

/-- Products of entries over a subrange are at least `1`. -/
private theorem prod_eVal_one_le (l : List ℕ) (hprime : ∀ x ∈ l, x.Prime)
    (I : Finset ℕ) (hI : I ⊆ Finset.range l.length) :
    1 ≤ ∏ i ∈ I, eVal l i := by
  apply Finset.one_le_prod
  intro i hi
  have hi' : i < l.length := by
    have h := hI hi
    rwa [Finset.mem_range] at h
  exact eVal_ge_one l hprime i hi'

/-- The Euclid number `N_I` is at least `2`, so it has a prime divisor. -/
private theorem euclidN_ge_two (l : List ℕ) (hprime : ∀ x ∈ l, x.Prime)
    (I : Finset ℕ) (hI : I ⊆ Finset.range l.length) :
    2 ≤ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i := by
  have h1 := prod_eVal_one_le l hprime I hI
  have h2 : 1 ≤ ∏ i ∈ (Finset.range l.length \ I), eVal l i :=
    prod_eVal_one_le l hprime _ Finset.sdiff_subset
  omega

/-- A finite list is a valid partial generalized Euclid sequence from seed `P`:
it starts with an enumeration of `P`, has distinct prime entries, and every
entry at position `j ≥ P.card` divides a complementary-product sum of earlier
entries. -/
private def Good (P : Finset ℕ) (l : List ℕ) : Prop :=
  P.toList <+: l ∧ l.Nodup ∧ (∀ x ∈ l, x.Prime) ∧
    ∀ j, P.card ≤ j → ∀ hj : j < l.length,
      ∃ I, I ⊆ Finset.range j ∧
        l[j]'hj ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range j \ I), eVal l i

private theorem good_nil (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) : Good P P.toList := by
  refine ⟨List.prefix_refl _, Finset.nodup_toList P, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_toList] at hx
    exact hP x hx
  · intro j hj1 hj2
    rw [Finset.length_toList] at hj2
    omega

/-- Appending a prime divisor of `N_I` preserves validity. -/
private theorem good_append (P : Finset ℕ) (l : List ℕ) (hg : Good P l) (r : ℕ)
    (hrprime : r.Prime) (hrnotin : r ∉ l) (I : Finset ℕ)
    (hI : I ⊆ Finset.range l.length)
    (hrdvd : r ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i) :
    Good P (l ++ [r]) := by
  obtain ⟨hpref, hnod, hprime, hwit⟩ := hg
  have hpre : l <+: l ++ [r] := List.prefix_append l [r]
  refine ⟨hpref.trans hpre, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnod, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact fun h => hrnotin (h ▸ ha)
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hprime x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hrprime
  · intro j hj1 hj2
    rw [List.length_append, List.length_singleton] at hj2
    by_cases hjn : j < l.length
    · obtain ⟨J, hJ, hdvd⟩ := hwit j hj1 hjn
      have hval : ∀ i ∈ J, eVal l i = eVal (l ++ [r]) i := by
        intro i hi
        have hi' : i < l.length := by
          have h2 := hJ hi
          rw [Finset.mem_range] at h2
          exact lt_of_lt_of_le h2 (Nat.le_of_lt hjn)
        exact eVal_prefix l (l ++ [r]) hpre i hi'
      have hval2 : ∀ i ∈ Finset.range j \ J, eVal l i = eVal (l ++ [r]) i := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range] at hi
        have hi' : i < l.length := lt_of_lt_of_le hi.1 (Nat.le_of_lt hjn)
        exact eVal_prefix l (l ++ [r]) hpre i hi'
      have hj2' : j < (l ++ [r]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have hget : (l ++ [r])[j] = l[j] := by
        have e1 := eVal_prefix l (l ++ [r]) hpre j hjn
        rw [eVal_lt l j hjn, eVal_lt (l ++ [r]) j hj2'] at e1
        exact e1.symm
      rw [Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2] at hdvd
      rw [hget]
      exact ⟨J, hJ, hdvd⟩
    · have hjj : j = l.length := by omega
      subst hjj
      have hlen' : l.length < (l ++ [r]).length := by
        rw [List.length_append, List.length_singleton]
        exact Nat.lt_succ_self _
      have hget : (l ++ [r])[l.length] = r := by simp
      have hval : ∀ i ∈ I, eVal (l ++ [r]) i = eVal l i := by
        intro i hi
        have hi' : i < l.length := by
          have h := hI hi
          rwa [Finset.mem_range] at h
        exact (eVal_prefix l (l ++ [r]) hpre i hi').symm
      have hval2 : ∀ i ∈ Finset.range l.length \ I, eVal (l ++ [r]) i = eVal l i := by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_range] at hi
        exact (eVal_prefix l (l ++ [r]) hpre i hi.1).symm
      refine ⟨I, hI, ?_⟩
      rw [hget, Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2]
      exact hrdvd

private theorem geneuclid_reach_q_of_char_one (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q]
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ)
    (hchar : geneuclidQuadChar q (-(geneuclidProduct l : ZMod q)) = 1) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  have hn0 := geneuclidProduct_ne_zero_mod q l hg.2.2.1 hqnot
  have hminus0 : -(geneuclidProduct l : ZMod q) ≠ 0 := neg_ne_zero.mpr hn0
  have hsquare : IsSquare (-(geneuclidProduct l : ZMod q)) := by
    apply (quadraticChar_one_iff_isSquare hminus0).mp
    change (((quadraticChar (ZMod q)) (-(geneuclidProduct l : ZMod q)) : ℤ) : ℂ) = 1 at hchar
    exact_mod_cast hchar
  obtain ⟨x, hx⟩ := hsquare
  have hx0 : x ≠ 0 := by
    intro h
    apply hminus0
    simpa [h] using hx
  let u := Units.mk0 x hx0
  have hu : u ∈ geneuclidUnits q l := by simp [hfull]
  have hexpr : (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) = 0 := by
    change x + (geneuclidProduct l : ZMod q) / x = 0
    field_simp
    rw [pow_two, ← hx]
    ring
  have happ : GeneuclidAppendable l q :=
    (geneuclid_q_appendable_iff_expression_zero q l hg.2.2.1 hqnot).mpr ⟨u, hu, hexpr⟩
  obtain ⟨_hq, I, hI, hdvd⟩ := happ
  refine ⟨l ++ [q], List.prefix_append l [q], ?_,
    good_append P l hg q Fact.out hqnot I hI hdvd, by simp⟩
  simp

private theorem geneuclid_reach_q_of_full_nonexception (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q] (hq2 : q ≠ 2)
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ)
    (hexception : q ≠ 5 ∨ (geneuclidProduct l : ZMod q) ≠ 3) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  let n : ZMod q := geneuclidProduct l
  have hn0 : n ≠ 0 := geneuclidProduct_ne_zero_mod q l hg.2.2.1 hqnot
  by_cases hchar : geneuclidQuadChar q (-n) = 1
  · exact geneuclid_reach_q_of_char_one P l hg q hqnot hfull hchar
  · obtain ⟨x, hxchar⟩ := geneuclid_character_witness q hq2 n hn0 hexception
    have hxmem : x ∈ geneuclidUnits q l := by simp [hfull]
    obtain ⟨I, hI, hExpr⟩ := geneuclid_unit_expression q l x hxmem
    have hexpr0 : (x : ZMod q) + n / (x : ZMod q) ≠ 0 := by
      intro hz
      have hsquare : IsSquare (-n) := by
        refine ⟨(x : ZMod q), ?_⟩
        field_simp at hz
        linear_combination -hz
      have hqchar : geneuclidQuadChar q (-n) = 1 := by
        change (((quadraticChar (ZMod q)) (-n) : ℤ) : ℂ) = 1
        exact_mod_cast (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hn0)).mpr hsquare
      exact hchar hqchar
    have hm0 : geneuclidN l I ≠ 0 := by
      have hge := euclidN_ge_two l hg.2.2.1 I hI
      simp only [geneuclidN]
      omega
    have hmchar : geneuclidQuadChar q ((geneuclidN l I : ℕ) : ZMod q) ≠ 1 := by
      rw [← hExpr]
      exact hxchar
    obtain ⟨p, hpprime, hpdvd, hpchar⟩ :=
      geneuclid_exists_prime_factor_map_ne_one
        (fun m : ℕ => geneuclidQuadChar q (m : ZMod q)) (by simp)
        (fun a b => by simp) hm0 hmchar
    have hpnot : p ∉ l :=
      fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
    have hpq : p ≠ q := by
      intro hpq
      subst p
      have hcast0 : (geneuclidN l I : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mpr hpdvd
      apply hexpr0
      rw [show n = (geneuclidProduct l : ZMod q) by rfl, hExpr]
      exact hcast0
    let l' := l ++ [p]
    have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
    have hqnot' : q ∉ l' := by simp [l', hqnot, hpq.symm]
    have hfull' : geneuclidUnits q l' = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      apply geneuclidUnits_append_subset q l p
      simp [hfull]
    have hnchar := geneuclidQuadChar_eq_neg_one_of_ne_one q (neg_ne_zero.mpr hn0) hchar
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro hp0
      have hqp : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp hp0
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hpprime).mp hqp).symm
    have hpchar' := geneuclidQuadChar_eq_neg_one_of_ne_one q hp0 hpchar
    have hchar' : geneuclidQuadChar q (-(geneuclidProduct l' : ZMod q)) = 1 := by
      rw [geneuclidProduct_append, Nat.cast_mul]
      rw [← neg_mul]
      change geneuclidQuadChar q (-n * (p : ZMod q)) = 1
      rw [map_mul, hnchar, hpchar']
      norm_num
    obtain ⟨l'', hpref, hlen, hgood, hqmem⟩ :=
      geneuclid_reach_q_of_char_one P l' hg' q hqnot' hfull' hchar'
    exact ⟨l'', (List.prefix_append l [p]).trans hpref,
      lt_trans (by simp [l']) hlen, hgood, hqmem⟩

private theorem geneuclid_reach_q_of_full (P : Finset ℕ) (l : List ℕ)
    (hg : Good P l) (q : ℕ) [Fact q.Prime] [NeZero q] (hq2 : q ≠ 2)
    (hqnot : q ∉ l) (hfull : geneuclidUnits q l = Finset.univ) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  by_cases hexception : q ≠ 5 ∨ (geneuclidProduct l : ZMod q) ≠ 3
  · exact geneuclid_reach_q_of_full_nonexception P l hg q hq2 hqnot hfull hexception
  · push Not at hexception
    obtain ⟨rfl, hn3⟩ := hexception
    let I : Finset ℕ := ∅
    have hI : I ⊆ Finset.range l.length := Finset.empty_subset _
    have hm0 : geneuclidN l I ≠ 0 := by
      have hge := euclidN_ge_two l hg.2.2.1 I hI
      simp only [geneuclidN]
      omega
    have h3zero : (3 : ZMod 5) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat, ZMod.val_one] at hval
    have h4zero : (4 : ZMod 5) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat] at hval
    have h4one : (4 : ZMod 5) ≠ 1 := by
      intro h
      have hval := congrArg ZMod.val h
      norm_num [ZMod.val_ofNat, ZMod.val_one] at hval
    have hmres : ((geneuclidN l I : ℕ) : ZMod 5) ≠ 1 := by
      change ((1 + geneuclidProduct l : ℕ) : ZMod 5) ≠ 1
      rw [Nat.cast_add, Nat.cast_one, hn3]
      intro h
      apply h4one
      calc
        (4 : ZMod 5) = 1 + 3 := by norm_num
        _ = 1 := h
    have hmres0 : ((geneuclidN l I : ℕ) : ZMod 5) ≠ 0 := by
      change ((1 + geneuclidProduct l : ℕ) : ZMod 5) ≠ 0
      rw [Nat.cast_add, Nat.cast_one, hn3]
      intro h
      apply h4zero
      calc
        (4 : ZMod 5) = 1 + 3 := by norm_num
        _ = 0 := h
    obtain ⟨p, hpprime, hpdvd, hpres⟩ :=
      geneuclid_exists_prime_factor_map_ne_one (fun m : ℕ => (m : ZMod 5))
        (by norm_num) (fun a b => by simp) hm0 hmres
    have hpnot : p ∉ l :=
      fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
    have hp5 : p ≠ 5 := by
      intro hp5
      subst p
      apply hmres0
      exact (ZMod.natCast_eq_zero_iff (geneuclidN l I) 5).mpr hpdvd
    let l' := l ++ [p]
    have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
    have h5not' : 5 ∉ l' := by simp [l', hqnot, hp5.symm]
    have hfull' : geneuclidUnits 5 l' = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      apply geneuclidUnits_append_subset 5 l p
      simp [hfull]
    have hn3' : (geneuclidProduct l' : ZMod 5) ≠ 3 := by
      rw [geneuclidProduct_append, Nat.cast_mul, hn3]
      intro h
      apply hpres
      exact mul_left_cancel₀ h3zero h
    obtain ⟨l'', hpref, hlen, hgood, h5mem⟩ :=
      geneuclid_reach_q_of_full_nonexception P l' hg' 5 (by norm_num) h5not' hfull'
        (Or.inr hn3')
    exact ⟨l'', (List.prefix_append l [p]).trans hpref,
      lt_trans (by simp [l']) hlen, hgood, h5mem⟩

/-- From any valid list, one valid step produces a new prime. -/
private theorem step_extend (P : Finset ℕ) (l : List ℕ) (hg : Good P l)
    (I : Finset ℕ) (hI : I ⊆ Finset.range l.length) :
    ∃ r, r.Prime ∧ r ∉ l ∧
      r ∣ (∏ i ∈ I, eVal l i) + ∏ i ∈ (Finset.range l.length \ I), eVal l i ∧
      Good P (l ++ [r]) := by
  have hN := euclidN_ge_two l hg.2.2.1 I hI
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hN)
  have hrnotin : r ∉ l :=
    fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI r hrprime hrdvd
  exact ⟨r, hrprime, hrnotin, hrdvd, good_append P l hg r hrprime hrnotin I hI hrdvd⟩

/-- Euclid's argument: some prime is always missing. -/
private theorem exists_fresh (l : List ℕ) (hnod : l.Nodup) (hprime : ∀ x ∈ l, x.Prime) :
    ∃ r, r.Prime ∧ r ∉ l := by
  have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
  have hN := euclidN_ge_two l hprime ∅ hI
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hN)
  exact ⟨r, hrprime, fresh_of_dvd_euclid l hnod hprime ∅ hI r hrprime hrdvd⟩

/-- A product of odd numbers is odd. -/
private theorem odd_finset_prod (s : Finset ℕ) (f : ℕ → ℕ) (h : ∀ i ∈ s, Odd (f i)) :
    Odd (∏ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact odd_one
  | insert a s hnot ihm =>
    rw [Finset.prod_insert hnot]
    exact Odd.mul (h _ (Finset.mem_insert_self _ _))
      (ihm (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- If `2` is missing, one valid step adjoins it (Booker's Proposition, `q = 2`
case: the product of odd primes is odd, so `P + 1` is even). -/
private theorem reach_two (P : Finset ℕ) (l : List ℕ) (hg : Good P l) (h2 : 2 ∉ l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ 2 ∈ l' := by
  have hprime : ∀ x ∈ l, x.Prime := hg.2.2.1
  have hodd : ∀ x ∈ l, Odd x := by
    intro x hx
    have hne : x ≠ 2 := fun h => h2 (h ▸ hx)
    exact (hprime x hx).odd_of_ne_two hne
  have hB : Odd (∏ i ∈ Finset.range l.length, eVal l i) := by
    apply odd_finset_prod
    intro i hi
    rw [Finset.mem_range] at hi
    rw [eVal_lt l i hi]
    exact hodd _ (List.getElem_mem hi)
  have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
  have heven : Even ((∏ i ∈ (∅ : Finset ℕ), eVal l i) +
      ∏ i ∈ (Finset.range l.length \ ∅), eVal l i) := by
    rw [Finset.prod_empty, Finset.sdiff_empty]
    exact odd_one.add_odd hB
  have hdvd : 2 ∣ (∏ i ∈ (∅ : Finset ℕ), eVal l i) +
      ∏ i ∈ (Finset.range l.length \ ∅), eVal l i := even_iff_two_dvd.mp heven
  refine ⟨l ++ [2], List.prefix_append l [2], ?_,
    good_append P l hg 2 Nat.prime_two h2 ∅ hI hdvd, by simp⟩
  rw [List.length_append, List.length_singleton]
  exact Nat.lt_succ_self _

private theorem reach_odd (P : Finset ℕ) (l : List ℕ) (hg : Good P l)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hmin : ∀ p, p.Prime → p < q → p ∈ l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧ q ∈ l' := by
  by_cases hqmem : q ∈ l
  · have hI : (∅ : Finset ℕ) ⊆ Finset.range l.length := Finset.empty_subset _
    obtain ⟨r, _hrprime, _hrnot, _hrdvd, hg'⟩ := step_extend P l hg ∅ hI
    refine ⟨l ++ [r], List.prefix_append l [r], by simp, hg', ?_⟩
    exact List.mem_append.mpr (Or.inl hqmem)
  let _ : Fact q.Prime := ⟨hq⟩
  let _ : NeZero q := ⟨hq.ne_zero⟩
  let deficit (xs : List ℕ) := Fintype.card (ZMod q)ˣ - (geneuclidUnits q xs).card
  generalize hk : deficit l = k
  induction k using Nat.strong_induction_on generalizing l with
  | h k ih =>
      by_cases hqapp : GeneuclidAppendable l q
      · obtain ⟨_hqprime, I, hI, hqdvd⟩ := hqapp
        refine ⟨l ++ [q], List.prefix_append l [q], by simp,
          good_append P l hg q hq hqmem I hI hqdvd, by simp⟩
      · let S := geneuclidUnits q l
        let H := MulAction.stabilizer (ZMod q)ˣ S
        by_cases hgrow : ∃ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0),
            GeneuclidAppendable l p ∧ Units.mk0 (p : ZMod q) hp0 ∉ H
        · obtain ⟨p, hp0, hpapp, hpH⟩ := hgrow
          obtain ⟨hpprime, I, hI, hpdvd⟩ := hpapp
          have hpnot : p ∉ l :=
            fresh_of_dvd_euclid l hg.2.1 hg.2.2.1 I hI p hpprime hpdvd
          have hpq : p ≠ q := by
            intro hpq
            subst p
            exact hqapp ⟨hq, I, hI, hpdvd⟩
          let l' := l ++ [p]
          have hg' : Good P l' := good_append P l hg p hpprime hpnot I hI hpdvd
          have hqmem' : q ∉ l' := by simp [l', hqmem, hpq.symm]
          have hmin' : ∀ r, r.Prime → r < q → r ∈ l' := by
            intro r hr hrq
            exact List.mem_append.mpr (Or.inl (hmin r hr hrq))
          have hsubset : S ⊆ geneuclidUnits q l' := by
            exact geneuclidUnits_append_subset q l p
          have houtside : ∃ u ∈ S,
              u * Units.mk0 (p : ZMod q) hp0 ∉ S := by
            rw [MulAction.mem_stabilizer_finset'] at hpH
            push Not at hpH
            obtain ⟨u, hu, hpu⟩ := hpH
            refine ⟨u, hu, ?_⟩
            simpa [smul_eq_mul, mul_comm] using hpu
          obtain ⟨u, hu, huout⟩ := houtside
          have hunew : u * Units.mk0 (p : ZMod q) hp0 ∈ geneuclidUnits q l' := by
            exact geneuclidUnits_mul_mk0_mem_append q l p hp0 u hu
          have hstrict : S ⊂ geneuclidUnits q l' := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hsubset, ?_⟩
            intro heq
            apply huout
            rwa [heq]
          have hcardlt : S.card < (geneuclidUnits q l').card :=
            Finset.card_lt_card hstrict
          have htotal : (geneuclidUnits q l').card ≤ Fintype.card (ZMod q)ˣ :=
            Finset.card_le_univ _
          have holdtotal : S.card < Fintype.card (ZMod q)ˣ :=
            hcardlt.trans_le htotal
          have hdlt : deficit l' < k := by
            rw [← hk]
            simp only [deficit]
            exact Nat.sub_lt_sub_left holdtotal hcardlt
          obtain ⟨l'', hpref, hlen, hgood, hqmem''⟩ :=
            ih (deficit l') hdlt l' hg' hmin' hqmem' rfl
          exact ⟨l'', (List.prefix_append l [p]).trans hpref,
            lt_trans (by simp [l']) hlen, hgood, hqmem''⟩
        · have hstable : ∀ (p : ℕ) (hp0 : (p : ZMod q) ≠ 0),
              GeneuclidAppendable l p → Units.mk0 (p : ZMod q) hp0 ∈ H := by
            intro p hp0 hpapp
            by_contra hpH
            exact hgrow ⟨p, hp0, hpapp, hpH⟩
          have hfull : geneuclidUnits q l = Finset.univ :=
            geneuclid_stable_units_eq_univ q hq2 l hg.2.2.1 hqmem hmin hqapp hstable
          exact geneuclid_reach_q_of_full P l hg q hq2 hqmem hfull

/-- The smallest missing prime can be adjoined by finitely many valid steps. -/
private theorem prop_reach (P : Finset ℕ) (l : List ℕ) (hg : Good P l) :
    ∃ l', l <+: l' ∧ l.length < l'.length ∧ Good P l' ∧
      sInf {p | p.Prime ∧ p ∉ l} ∈ l' := by
  have hne : {p | p.Prime ∧ p ∉ l}.Nonempty := by
    obtain ⟨r, hrp, hrn⟩ := exists_fresh l hg.2.1 hg.2.2.1
    exact ⟨r, hrp, hrn⟩
  have hqP : (sInf {p | p.Prime ∧ p ∉ l}).Prime ∧
      sInf {p | p.Prime ∧ p ∉ l} ∉ l := Nat.sInf_mem hne
  obtain ⟨hqprime, hqnotin⟩ := hqP
  have hmin : ∀ p, p.Prime → p < sInf {p | p.Prime ∧ p ∉ l} → p ∈ l := by
    intro m hmp hmlt
    by_contra hnin
    have hmem : m ∈ {p | p.Prime ∧ p ∉ l} := ⟨hmp, hnin⟩
    have hle := Nat.sInf_le hmem
    omega
  rcases eq_or_ne (sInf {p | p.Prime ∧ p ∉ l}) 2 with h2 | h2
  · obtain ⟨l', hp, hlen, hg', hm⟩ :=
      reach_two P l hg (by rwa [h2] at hqnotin)
    exact ⟨l', hp, hlen, hg', by rwa [h2]⟩
  · obtain ⟨l', hp, hlen, hg', hm⟩ := reach_odd P l hg _ hqprime h2 hmin
    exact ⟨l', hp, hlen, hg', hm⟩

/-- One stage of the construction: adjoin the smallest missing prime. -/
private noncomputable def chainStep (P : Finset ℕ) (x : { l : List ℕ // Good P l }) :
    { l : List ℕ // Good P l } :=
  ⟨Classical.choose (prop_reach P x.1 x.2),
    (Classical.choose_spec (prop_reach P x.1 x.2)).2.2.1⟩

/-- The nested tower of partial sequences. -/
private noncomputable def Chain (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ℕ → { l : List ℕ // Good P l }
  | 0 => ⟨P.toList, good_nil P hP⟩
  | n + 1 => chainStep P (Chain P hP n)

private noncomputable def chainL (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) : List ℕ :=
  (Chain P hP n).1

private theorem chainL_good (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    Good P (chainL P hP n) :=
  (Chain P hP n).2

private theorem chainL_succ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP (n + 1) =
      Classical.choose (prop_reach P (chainL P hP n) (chainL_good P hP n)) := by
  simp only [chainL, Chain, chainStep]

private theorem chainL_step (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP n <+: chainL P hP (n + 1) := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).1
  rw [← chainL_succ P hP n] at h
  exact h

private theorem chainL_lt (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    (chainL P hP n).length < (chainL P hP (n + 1)).length := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).2.1
  rw [← chainL_succ P hP n] at h
  exact h

private theorem chainL_qmem (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP n} ∈ chainL P hP (n + 1) := by
  have h := (Classical.choose_spec
    (prop_reach P (chainL P hP n) (chainL_good P hP n))).2.2.2
  rw [← chainL_succ P hP n] at h
  exact h

private theorem chainL_spec (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    chainL P hP n <+: chainL P hP (n + 1) ∧
      (chainL P hP n).length < (chainL P hP (n + 1)).length ∧
      sInf {p | p.Prime ∧ p ∉ chainL P hP n} ∈ chainL P hP (n + 1) :=
  ⟨chainL_step P hP n, chainL_lt P hP n, chainL_qmem P hP n⟩

private theorem chainL_prefix_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s t : ℕ)
    (h : s ≤ t) : chainL P hP s <+: chainL P hP t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact ih.trans (chainL_step P hP _)

private theorem chainL_len (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    P.card + n ≤ (chainL P hP n).length := by
  induction n with
  | zero => simp [chainL, Chain, Finset.length_toList]
  | succ n ih =>
    have hlt := (chainL_spec P hP n).2.1
    omega

private theorem chainL_eval_stable (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i s t : ℕ)
    (hs : i < (chainL P hP s).length) (hst : s ≤ t) :
    eVal (chainL P hP s) i = eVal (chainL P hP t) i :=
  eVal_prefix _ _ (chainL_prefix_le P hP s t hst) i hs

private theorem prefix_mem {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) (a : ℕ) (hm : a ∈ l₁) :
    a ∈ l₂ := by
  have heq := List.prefix_iff_eq_append.mp h
  rw [← heq]
  exact List.mem_append.mpr (Or.inl hm)

/-- The final sequence: stabilization of the tower. -/
private noncomputable def seqA (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i : ℕ) : ℕ :=
  eVal (chainL P hP (i + 1)) i

private theorem seqA_eq (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i t : ℕ)
    (ht : i + 1 ≤ t) : seqA P hP i = eVal (chainL P hP t) i := by
  change eVal (chainL P hP (i + 1)) i = _
  exact chainL_eval_stable P hP i (i + 1) t
    (by have h := chainL_len P hP (i + 1); omega) ht

private theorem seqA_prime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i : ℕ) :
    (seqA P hP i).Prime := by
  have hlen : i < (chainL P hP (i + 1)).length := by
    have h := chainL_len P hP (i + 1); omega
  rw [seqA_eq P hP i (i + 1) le_rfl, eVal_lt _ _ hlen]
  exact (chainL_good P hP (i + 1)).2.2.1 _ (List.getElem_mem hlen)

private theorem seqA_injective (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (seqA P hP) := by
  intro i j hij
  rcases le_total i j with hle | hle
  · have hi : i < (chainL P hP (j + 1)).length := by
      have h := chainL_len P hP (j + 1); omega
    have hj : j < (chainL P hP (j + 1)).length := by
      have h := chainL_len P hP (j + 1); omega
    have e1 := seqA_eq P hP i (j + 1) (by omega)
    have e2 := seqA_eq P hP j (j + 1) le_rfl
    rw [eVal_lt _ _ hi] at e1
    rw [eVal_lt _ _ hj] at e2
    have heq : (chainL P hP (j + 1))[i] = (chainL P hP (j + 1))[j] := by
      rw [← e1, ← e2]; exact hij
    exact (List.Nodup.getElem_inj_iff (chainL_good P hP (j + 1)).2.1).mp heq
  · have hi : i < (chainL P hP (i + 1)).length := by
      have h := chainL_len P hP (i + 1); omega
    have hj : j < (chainL P hP (i + 1)).length := by
      have h := chainL_len P hP (i + 1); omega
    have e1 := seqA_eq P hP i (i + 1) le_rfl
    have e2 := seqA_eq P hP j (i + 1) (by omega)
    rw [eVal_lt _ _ hi] at e1
    rw [eVal_lt _ _ hj] at e2
    have heq : (chainL P hP (i + 1))[j] = (chainL P hP (i + 1))[i] := by
      rw [← e1, ← e2]; exact hij.symm
    exact ((List.Nodup.getElem_inj_iff (chainL_good P hP (i + 1)).2.1).mp heq).symm

private theorem seqA_mem_seed (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (i : ℕ)
    (hi : i < P.card) : seqA P hP i ∈ P := by
  have hlen0 : i < P.toList.length := by rwa [Finset.length_toList]
  have h0 : chainL P hP 0 = P.toList := rfl
  have hpre : P.toList <+: chainL P hP (i + 1) := by
    have h := chainL_prefix_le P hP 0 (i + 1) (Nat.zero_le _)
    rwa [h0] at h
  have e1 := seqA_eq P hP i (i + 1) le_rfl
  have e2 := eVal_prefix P.toList (chainL P hP (i + 1)) hpre i hlen0
  rw [eVal_lt P.toList i hlen0] at e2
  rw [e1, ← e2]
  exact Finset.mem_toList.mp (List.getElem_mem hlen0)

private theorem seqA_cover_seed (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (p : ℕ)
    (hp : p ∈ P) : ∃ i < P.card, seqA P hP i = p := by
  have hmem : p ∈ P.toList := Finset.mem_toList.mpr hp
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  have hiC : i < P.card := by
    have h := Finset.length_toList P; omega
  refine ⟨i, hiC, ?_⟩
  have h0 : chainL P hP 0 = P.toList := rfl
  have hpre : P.toList <+: chainL P hP (i + 1) := by
    have h := chainL_prefix_le P hP 0 (i + 1) (Nat.zero_le _)
    rwa [h0] at h
  have e1 := seqA_eq P hP i (i + 1) le_rfl
  have e2 := eVal_prefix P.toList (chainL P hP (i + 1)) hpre i hi
  have e3 := eVal_lt P.toList i hi
  rw [e1, ← e2, e3, heq]

private theorem seqA_step (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ)
    (hn : P.card ≤ n) :
    ∃ I : Finset ℕ, I ⊆ Finset.range n ∧
      seqA P hP n ∣ (∏ i ∈ I, seqA P hP i) + ∏ i ∈ (Finset.range n \ I), seqA P hP i := by
  have hlen : n < (chainL P hP (n + 1)).length := by
    have h := chainL_len P hP (n + 1); omega
  obtain ⟨I, hI, hdvd⟩ := (chainL_good P hP (n + 1)).2.2.2 n hn hlen
  refine ⟨I, hI, ?_⟩
  have han : seqA P hP n = (chainL P hP (n + 1))[n] := by
    rw [seqA_eq P hP n (n + 1) le_rfl]
    exact eVal_lt _ _ hlen
  have hval : ∀ i ∈ I, seqA P hP i = eVal (chainL P hP (n + 1)) i := by
    intro i hi
    have hi' : i < n := by
      have h := hI hi
      rwa [Finset.mem_range] at h
    exact seqA_eq P hP i (n + 1) (by omega)
  have hval2 : ∀ i ∈ Finset.range n \ I, seqA P hP i = eVal (chainL P hP (n + 1)) i := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range] at hi
    exact seqA_eq P hP i (n + 1) (by omega)
  rw [han, Finset.prod_congr rfl hval, Finset.prod_congr rfl hval2]
  exact hdvd

private theorem chainL_qprop (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    (sInf {p | p.Prime ∧ p ∉ chainL P hP s}).Prime ∧
      sInf {p | p.Prime ∧ p ∉ chainL P hP s} ∉ chainL P hP s := by
  have hne : {p | p.Prime ∧ p ∉ chainL P hP s}.Nonempty := by
    obtain ⟨r, hrp, hrn⟩ := exists_fresh _ (chainL_good P hP s).2.1 (chainL_good P hP s).2.2.1
    exact ⟨r, hrp, hrn⟩
  exact Nat.sInf_mem hne

private theorem chainL_qstrict (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP s} <
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := by
  have hmem : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ∈ chainL P hP (s + 1) :=
    (chainL_spec P hP s).2.2
  have hnot := (chainL_qprop P hP (s + 1)).2
  have hne : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ≠
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := fun h => hnot (h ▸ hmem)
  have hle : sInf {p | p.Prime ∧ p ∉ chainL P hP s} ≤
      sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    have hnotin : sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} ∉ chainL P hP s := by
      intro hin
      exact hnot (prefix_mem (chainL_step P hP s) _ hin)
    have hmem2 : sInf {p | p.Prime ∧ p ∉ chainL P hP (s + 1)} ∈
        {p | p.Prime ∧ p ∉ chainL P hP s} :=
      ⟨(chainL_qprop P hP (s + 1)).1, hnotin⟩
    have hle2 := Nat.sInf_le hmem2
    omega
  exact lt_of_le_of_ne hle hne

private theorem chainL_qgrowth (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s : ℕ) :
    sInf {p | p.Prime ∧ p ∉ chainL P hP 0} + s ≤
      sInf {p | p.Prime ∧ p ∉ chainL P hP s} := by
  induction s with
  | zero => exact Nat.le_refl _
  | succ s ih =>
    have hlt := chainL_qstrict P hP s
    omega

private theorem chainL_cover (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (q : ℕ)
    (hq : q.Prime) : q ∈ chainL P hP (q + 1) := by
  by_contra hnin
  have hmem : q ∈ {p | p.Prime ∧ p ∉ chainL P hP (q + 1)} := ⟨hq, hnin⟩
  have hle := Nat.sInf_le hmem
  have hg := chainL_qgrowth P hP (q + 1)
  omega

private theorem seqA_cover_all (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (p : ℕ)
    (hp : p.Prime) : ∃ i, seqA P hP i = p := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp (chainL_cover P hP p hp)
  refine ⟨i, ?_⟩
  have h3 : seqA P hP i = eVal (chainL P hP (i + 1)) i := rfl
  have h2 : eVal (chainL P hP (p + 1)) i = p := by
    rw [eVal_lt _ _ hi]; exact heq
  rcases le_total (i + 1) (p + 1) with hle | hle
  · have h1 : eVal (chainL P hP (i + 1)) i = eVal (chainL P hP (p + 1)) i :=
      eVal_prefix _ _ (chainL_prefix_le P hP (i + 1) (p + 1) hle) i
        (by have h := chainL_len P hP (i + 1); omega)
    rw [h3, h1, h2]
  · have h1 : eVal (chainL P hP (p + 1)) i = eVal (chainL P hP (i + 1)) i :=
      eVal_prefix _ _ (chainL_prefix_le P hP (p + 1) (i + 1) hle) i hi
    rw [h3, ← h1, h2]

/--
For any finite set `P` of primes there is a generalized Euclid sequence
with seed `P` (each new term a prime divisor of
`∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` for some `I`) containing every prime.

Source: Andrew R. Booker, "A Variant of the Euclid-Mullin Sequence
Containing Every Prime," Journal of Integer Sequences 19 (2016),
Article 16.6.4, Theorem (label t:main), lines 132–136,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Booker/book3.tex

The source's construction: for primes `p_1, …, p_k` and any
`I ⊆ {1, …, k}`, `N_I = ∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` is coprime to
the previous product, so a prime divisor of `N_I` is always new; the
sequence is zero-indexed here with the first `P.card` terms enumerating
the seed. This is an existence claim over all choices of `I` and prime
divisor, unlike the open Euclid–Mullin conjecture about one specific
sequence.

Proves `Wanted` entry `generalized_euclid_sequence_contains_every_prime`.

Proof: Booker's residue-set route, with an elementary squarefree count in place of Rogers'
density bound and Jacobi-sum character-sum bounds in place of the Hasse and Weil bounds.
-/
public theorem generalized_euclid_sequence_contains_every_prime
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∃ a : ℕ → ℕ, (∀ i, Nat.Prime (a i)) ∧ Function.Injective a ∧
      (∀ i < P.card, a i ∈ P) ∧ (∀ p ∈ P, ∃ i < P.card, a i = p) ∧
      (∀ n, P.card ≤ n → ∃ I : Finset ℕ, I ⊆ Finset.range n ∧
        a n ∣ (∏ i ∈ I, a i) + ∏ i ∈ (Finset.range n \ I), a i) ∧
      (∀ p, Nat.Prime p → ∃ i, a i = p) := by
  exact ⟨seqA P hP, seqA_prime P hP, seqA_injective P hP, seqA_mem_seed P hP,
    seqA_cover_seed P hP, seqA_step P hP, seqA_cover_all P hP⟩


end MetaMathlibExt
