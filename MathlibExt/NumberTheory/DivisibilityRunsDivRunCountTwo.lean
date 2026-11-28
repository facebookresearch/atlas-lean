/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.DivRunCountFour
public import MathlibExt.NumberTheory.DivisibilityRuns
public import MathlibExt.NumberTheory.GeneralizedTribonacciBasis
public import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact formula for the length-two run count

For every natural number `B`, let `S(B) = ∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1)` and let
`A_B(2)` be the number of integer tuples `(x, y, a, b, c) ∈ [-B, B]^5` with `(x, y) ≠ (0, 0)`
and `(a, b, c) ≠ (0, 0, 0)` that have a divisibility run of length at least `2`. Then
`S(B) = 2 * ∑ m ∈ Finset.Icc 1 B, B / m + B` and
`A_B(2) = 4 * (2 * B + 1) * S(B)^2 - 4 * B^2`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`).
-/

@[expose] public section

namespace MetaMathlibExt

namespace divRunCount_two

private theorem mem_Icc_iff_natAbs_le (a : ℤ) (B : ℕ) :
    a ∈ Finset.Icc (-(B : ℤ)) B ↔ a.natAbs ≤ B := by
  simp only [Finset.mem_Icc]
  omega

private theorem card_Icc_neg_self (K : ℕ) :
    (Finset.Icc (-(K : ℤ)) K).card = 2 * K + 1 := by
  have hle : -(K : ℤ) ≤ (K : ℤ) + 1 := by omega
  have h : ((Finset.Icc (-(K : ℤ)) K).card : ℤ) = ((2 * K + 1 : ℕ) : ℤ) := by
    rw [Int.card_Icc_of_le _ _ hle]
    push_cast
    ring
  exact_mod_cast h

private theorem card_filter_dvd_eq (B : ℕ) (x : ℤ) (hx : x ≠ 0) :
    ((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card = 2 * (B / x.natAbs) + 1 := by
  have hbij : ((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card
      = (Finset.Icc (-(((B / x.natAbs : ℕ)) : ℤ)) ((B / x.natAbs : ℕ))).card := by
    apply Finset.card_bij' (fun a _ => a / x) (fun k _ => x * k)
    · intro a ha
      simp only [Finset.mem_filter] at ha
      obtain ⟨haI, hdvd⟩ := ha
      rw [mem_Icc_iff_natAbs_le, Int.natAbs_ediv_of_dvd hdvd]
      exact Nat.div_le_div_right ((mem_Icc_iff_natAbs_le a B).mp haI)
    · intro k hk
      simp only [Finset.mem_filter]
      have hkle : k.natAbs ≤ B / x.natAbs := (mem_Icc_iff_natAbs_le k _).mp hk
      refine ⟨(mem_Icc_iff_natAbs_le _ _).mpr ?_, dvd_mul_right x k⟩
      rw [Int.natAbs_mul]
      calc x.natAbs * k.natAbs ≤ x.natAbs * (B / x.natAbs) := Nat.mul_le_mul le_rfl hkle
        _ = B / x.natAbs * x.natAbs := by rw [mul_comm]
        _ ≤ B := Nat.div_mul_le_self B x.natAbs
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact Int.mul_ediv_cancel' ha.2
    · intro k _
      exact Int.mul_ediv_cancel_left k hx
  rw [hbij, card_Icc_neg_self]

private theorem card_filter_dvd (B : ℕ) (x y : ℤ) :
    ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter
      fun t => x ∣ t.1 ∧ y ∣ t.2.1).card
    = ((Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a)).card
      * (((Finset.Icc (-(B : ℤ)) B).filter (fun b => y ∣ b)).card
        * (Finset.Icc (-(B : ℤ)) B).card) := by
  have hset : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter
        (fun t => x ∣ t.1 ∧ y ∣ t.2.1)
      = (Finset.Icc (-(B : ℤ)) B).filter (fun a => x ∣ a) ×ˢ
        (Finset.Icc (-(B : ℤ)) B).filter (fun b => y ∣ b) ×ˢ Finset.Icc (-(B : ℤ)) B := by
    ext ⟨a, b, c⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hset, Finset.card_product, Finset.card_product]

private theorem triple_closed (B : ℕ) (x y : ℤ) :
    (∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B,
      if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
        IsDivRunUpTo x y t.1 t.2.1 t.2.2 2 then (1 : ℤ) else 0)
    = if x ≠ 0 ∧ y ≠ 0 then
        (((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) * ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ)
          * ((2 * B + 1 : ℕ) : ℤ) - 1)
      else 0 := by
  by_cases hc : x ≠ 0 ∧ y ≠ 0
  · rw [ite_eq_left hc]
    obtain ⟨hx, hy⟩ := hc
    have hmem : (0, 0, 0) ∈ (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t => x ∣ t.1 ∧ y ∣ t.2.1 := by
      simp [dvd_zero]
    have hfilter : (Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter (fun t =>
          (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
            IsDivRunUpTo x y t.1 t.2.1 t.2.2 2) =
        ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
          Finset.Icc (-(B : ℤ)) B).filter fun t => x ∣ t.1 ∧ y ∣ t.2.1).erase (0, 0, 0) := by
      ext t
      obtain ⟨a, b, c⟩ := t
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ht, -, htne, hrun⟩
        obtain ⟨⟨-, hqa⟩, -, hqb⟩ :=
          (isDivRunUpTo_small x y a b c).2.1.mp hrun
        exact ⟨htne, ht, hqa, hqb⟩
      · rintro ⟨htne, ht, hqa, hqb⟩
        exact ⟨ht, fun h => hx (Prod.ext_iff.mp h).1, htne,
          (isDivRunUpTo_small x y a b c).2.1.mpr ⟨⟨hx, hqa⟩, hy, hqb⟩⟩
    rw [← Finset.natCast_card_filter, hfilter, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
        Finset.Icc (-(B : ℤ)) B).filter fun t => x ∣ t.1 ∧ y ∣ t.2.1).card :=
      Finset.card_pos.mpr ⟨(0, 0, 0), hmem⟩
    rw [Nat.cast_sub hpos, card_filter_dvd, card_filter_dvd_eq B x hx, card_filter_dvd_eq B y hy,
      card_Icc_neg_self]
    push_cast
    ring
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro t _
    rw [ite_eq_right]
    rintro ⟨-, -, hrun⟩
    obtain ⟨⟨hx', -⟩, hy', -⟩ :=
      (isDivRunUpTo_small x y t.1 t.2.1 t.2.2).2.1.mp hrun
    exact hc ⟨hx', hy'⟩

private theorem sum_symmetric (B : ℕ) (f : ℕ → ℤ) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) B, (if x ≠ 0 then f x.natAbs else 0)
      = 2 * ∑ m ∈ Finset.Icc 1 B, f m := by
  induction B with
  | zero =>
    rw [Finset.Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty, mul_zero]
    simp
  | succ B ih =>
    have hI : Finset.Icc (-(((B + 1 : ℕ)) : ℤ)) (((B + 1 : ℕ)) : ℤ)
        = insert (-(((B + 1 : ℕ)) : ℤ))
          (insert (((B + 1 : ℕ)) : ℤ) (Finset.Icc (-((B : ℕ)) : ℤ) ((B : ℕ) : ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hpos : (((B + 1 : ℕ)) : ℤ) ∉ Finset.Icc (-((B : ℕ)) : ℤ) ((B : ℕ) : ℤ) := by
      intro h
      rw [Finset.mem_Icc] at h
      push_cast at h
      omega
    have hneg : (-(((B + 1 : ℕ)) : ℤ))
        ∉ insert (((B + 1 : ℕ)) : ℤ) (Finset.Icc (-((B : ℕ)) : ℤ) ((B : ℕ) : ℤ)) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_Icc] at h
      push_cast at h
      omega
    have hne : (((B + 1 : ℕ)) : ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero B
    have hne' : (-(((B + 1 : ℕ)) : ℤ)) ≠ 0 := neg_ne_zero.mpr hne
    have hnabs : ((((B + 1 : ℕ)) : ℤ)).natAbs = B + 1 := Int.natAbs_natCast (B + 1)
    have hnabs' : ((-(((B + 1 : ℕ)) : ℤ))).natAbs = B + 1 := by
      rw [Int.natAbs_neg, hnabs]
    rw [hI, Finset.sum_insert hneg, Finset.sum_insert hpos, ite_eq_left hne', ite_eq_left hne,
      hnabs', hnabs, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ B + 1)]
    ring

private theorem sum_ne_one (B : ℕ) :
    ∑ x ∈ Finset.Icc (-(B : ℤ)) B, (if x ≠ 0 then (1 : ℤ) else 0) = 2 * (B : ℤ) := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(B : ℤ)) B := by simp
  have hfilter : (Finset.Icc (-(B : ℤ)) B).filter (fun x => x ≠ 0)
      = (Finset.Icc (-(B : ℤ)) B).erase 0 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact and_comm
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_erase_of_mem h0,
    card_Icc_neg_self, Nat.add_sub_cancel]
  simp

private theorem double_sum (B : ℕ) :
    (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
      (if x ≠ 0 ∧ y ≠ 0 then
        (((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) * ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ)
          * ((2 * B + 1 : ℕ) : ℤ) - 1)
      else 0))
    = ((2 * B + 1 : ℕ) : ℤ)
        * ((∑ x ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0))
          * (∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if y ≠ 0 then ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ) else 0)))
      - (∑ x ∈ Finset.Icc (-(B : ℤ)) B, (if x ≠ 0 then (1 : ℤ) else 0))
        * (∑ y ∈ Finset.Icc (-(B : ℤ)) B, (if y ≠ 0 then (1 : ℤ) else 0)) := by
  have per_term : ∀ x y : ℤ,
      (if x ≠ 0 ∧ y ≠ 0 then
          (((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) * ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ)
            * ((2 * B + 1 : ℕ) : ℤ) - 1)
        else (0 : ℤ))
      = ((2 * B + 1 : ℕ) : ℤ)
          * ((if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0)
            * (if y ≠ 0 then ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ) else 0))
        - (if x ≠ 0 ∧ y ≠ 0 then (1 : ℤ) else 0) := by
    intro x y
    by_cases hx : x ≠ 0
    · by_cases hy : y ≠ 0
      · have hxy : x ≠ 0 ∧ y ≠ 0 := ⟨hx, hy⟩
        simp only [ite_eq_left hxy, ite_eq_left hx, ite_eq_left hy]
        ring
      · have hxy : ¬ (x ≠ 0 ∧ y ≠ 0) := fun h => hy h.2
        simp only [ite_eq_right hxy, ite_eq_left hx, ite_eq_right hy]
        ring
    · have hxy : ¬ (x ≠ 0 ∧ y ≠ 0) := fun h => hx h.1
      simp only [ite_eq_right hxy, ite_eq_right hx]
      ring
  have hsplit : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 then
          (((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) * ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ)
            * ((2 * B + 1 : ℕ) : ℤ) - 1)
        else (0 : ℤ)))
      = (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          ((2 * B + 1 : ℕ) : ℤ)
            * ((if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0)
              * (if y ≠ 0 then ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ) else 0)))
        - (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 then (1 : ℤ) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact per_term x y
  have hC : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        ((2 * B + 1 : ℕ) : ℤ)
          * ((if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0)
            * (if y ≠ 0 then ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ) else 0)))
      = ((2 * B + 1 : ℕ) : ℤ)
        * ((∑ x ∈ Finset.Icc (-(B : ℤ)) B,
            (if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0))
          * (∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            (if y ≠ 0 then ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ) else 0))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (Finset.mul_sum _ _ _).symm
  have hN : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
        (if x ≠ 0 ∧ y ≠ 0 then (1 : ℤ) else 0))
      = (∑ x ∈ Finset.Icc (-(B : ℤ)) B, (if x ≠ 0 then (1 : ℤ) else 0))
        * (∑ y ∈ Finset.Icc (-(B : ℤ)) B, (if y ≠ 0 then (1 : ℤ) else 0)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases hx : x ≠ 0
    · by_cases hy : y ≠ 0
      · have hxy : x ≠ 0 ∧ y ≠ 0 := ⟨hx, hy⟩
        simp only [ite_eq_left hxy, ite_eq_left hx, ite_eq_left hy]
        ring
      · have hxy : ¬ (x ≠ 0 ∧ y ≠ 0) := fun h => hy h.2
        simp only [ite_eq_right hxy, ite_eq_left hx, ite_eq_right hy]
        ring
    · have hxy : ¬ (x ≠ 0 ∧ y ≠ 0) := fun h => hx h.1
      simp only [ite_eq_right hxy, ite_eq_right hx]
      ring
  rw [hsplit, hC, hN]

end divRunCount_two

/-- **Exact formula for the length-two run count.** For every natural number $B$, let
$S(B) = \sum_{m=1}^{B} \left(2\lfloor B/m \rfloor + 1\right)$ and let $A_B(2)$ be the number of
integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $2$. Then
$S(B) = 2 \sum_{m=1}^{B} \lfloor B/m \rfloor + B$ and $A_B(2) = 4(2B+1) S(B)^2 - 4B^2$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem divRunCount_two (B : ℕ) :
    ∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) = 2 * ∑ m ∈ Finset.Icc 1 B, B / m + B ∧
      (divRunCount B 2 : ℤ)
        = 4 * (2 * B + 1) * (∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) : ℕ) ^ 2 - 4 * B ^ 2 := by
  refine ⟨?_, ?_⟩
  · have hcard : ∑ m ∈ Finset.Icc 1 B, (1 : ℕ) = B := by
      rw [← Finset.card_eq_sum_ones, Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcard]
  · have hdecomp : (divRunCount B 2 : ℤ) =
        ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          ∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
              Finset.Icc (-(B : ℤ)) B,
            if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
                IsDivRunUpTo x y t.1 t.2.1 t.2.2 2 then (1 : ℤ) else 0 := by
      unfold divRunCount
      rw [Finset.natCast_card_filter]
      simp only [Finset.sum_product]
    have hclosed : (∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          ∑ t ∈ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
              Finset.Icc (-(B : ℤ)) B,
            if (x, y) ≠ (0, 0) ∧ (t.1, t.2.1, t.2.2) ≠ (0, 0, 0) ∧
                IsDivRunUpTo x y t.1 t.2.1 t.2.2 2 then (1 : ℤ) else 0)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 ∧ y ≠ 0 then
            (((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) * ((2 * (B / y.natAbs) + 1 : ℕ) : ℤ)
              * ((2 * B + 1 : ℕ) : ℤ) - 1)
          else 0) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        divRunCount_two.triple_closed B x y
    have hS : (∑ x ∈ Finset.Icc (-(B : ℤ)) B,
          (if x ≠ 0 then ((2 * (B / x.natAbs) + 1 : ℕ) : ℤ) else 0))
        = 2 * ((∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) : ℕ) : ℤ) := by
      have h := divRunCount_two.sum_symmetric B (fun m : ℕ => ((2 * (B / m) + 1 : ℕ) : ℤ))
      simpa only [← Nat.cast_sum] using h
    rw [hdecomp, hclosed, divRunCount_two.double_sum, hS, divRunCount_two.sum_ne_one]
    push_cast
    ring

end MetaMathlibExt
