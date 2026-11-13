/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star

@[expose] public section

namespace MetaMathlibExt

/-! # Kaneko formula for poly-Bernoulli numbers, Bernoulli case
-/

-- Lemma L1: binomial-Stirling identity
private lemma stirling_binom_full (n m : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (Nat.stirlingSecond k m : ℚ)
      = (Nat.stirlingSecond (n + 1) (m + 1) : ℚ) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [Nat.stirlingSecond_self]
    | succ m => simp [Nat.stirlingSecond]
  | succ n ih =>
    cases m with
    | zero =>
      have h0 : ∀ k : ℕ, (Nat.stirlingSecond k 0 : ℚ) = if k = 0 then 1 else 0 := by
        intro k
        cases k with
        | zero => simp
        | succ k => simp [Nat.stirlingSecond_succ_zero]
      simp_rw [h0]
      simp [Nat.stirlingSecond_one_right]
    | succ m =>
      have hS : (Nat.stirlingSecond (n + 2) (m + 2) : ℚ)
          = (m + 2 : ℚ) * (Nat.stirlingSecond (n + 1) (m + 2) : ℚ)
            + (Nat.stirlingSecond (n + 1) (m + 1) : ℚ) := by
        have h := Nat.stirlingSecond_succ_succ (n + 1) (m + 1)
        simp only [show n + 1 + 1 = n + 2 from rfl, show m + 1 + 1 = m + 2 from rfl] at h
        rw [h]; push_cast; ring
      rw [hS, ← ih (m + 1), ← ih m]
      have pascal : ∀ k : ℕ, ((n + 1).choose (k + 1) : ℚ)
          = (n.choose k : ℚ) + (n.choose (k + 1) : ℚ) := by
        intro k
        have h := Nat.choose_succ_succ n k
        rw [h]; push_cast; ring
      have stir : ∀ k : ℕ, (Nat.stirlingSecond (k + 1) (m + 1) : ℚ)
          = (m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
            + (Nat.stirlingSecond k m : ℚ) := by
        intro k
        have h := Nat.stirlingSecond_succ_succ k m
        rw [h]; push_cast; ring
      have peel : ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℚ)
            * (Nat.stirlingSecond k (m + 1) : ℚ)
          = ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℚ)
            * (Nat.stirlingSecond (k + 1) (m + 1) : ℚ) := by
        have h := Finset.sum_range_succ'
          (fun k => ((n + 1).choose k : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)) (n + 1)
        rw [h]
        simp
      rw [peel]
      have first : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
            * ((m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
              + (Nat.stirlingSecond k m : ℚ))
          = (m + 1 : ℚ) * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
              * (Nat.stirlingSecond k (m + 1) : ℚ)
            + ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
              * (Nat.stirlingSecond k m : ℚ) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have reidx : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℚ)
            * (Nat.stirlingSecond (k + 1) (m + 1) : ℚ)
          = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
            * (Nat.stirlingSecond k (m + 1) : ℚ) := by
        have h1 := Finset.sum_range_succ'
          (fun k => (n.choose k : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)) (n + 1)
        have h2 := Finset.sum_range_succ
          (fun k => (n.choose k : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)) (n + 1)
        have f0 : (n.choose 0 : ℚ) * (Nat.stirlingSecond 0 (m + 1) : ℚ) = 0 := by simp
        have fn : (n.choose (n + 1) : ℚ) * (Nat.stirlingSecond (n + 1) (m + 1) : ℚ) = 0 := by
          have hc : n.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
          rw [hc, Nat.cast_zero, zero_mul]
        have h3 := h1.symm.trans h2
        rw [f0, fn, add_zero, add_zero] at h3
        exact h3
      have second : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℚ)
            * ((m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
              + (Nat.stirlingSecond k m : ℚ))
          = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
              * (Nat.stirlingSecond k (m + 1) : ℚ) := by
        have e : ∀ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℚ)
              * ((m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
                + (Nat.stirlingSecond k m : ℚ))
            = (n.choose (k + 1) : ℚ) * (Nat.stirlingSecond (k + 1) (m + 1) : ℚ) := by
          intro k _
          congr 1
          exact (stir k).symm
        rw [Finset.sum_congr rfl e]
        exact reidx
      have step1 : ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℚ)
            * (Nat.stirlingSecond (k + 1) (m + 1) : ℚ)
          = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ)
              * ((m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
                + (Nat.stirlingSecond k m : ℚ)))
          + (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℚ)
              * ((m + 1 : ℚ) * (Nat.stirlingSecond k (m + 1) : ℚ)
                + (Nat.stirlingSecond k m : ℚ))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [pascal k, stir k, add_mul]
      rw [step1, first, second]
      ring

private noncomputable def kanekoT (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
    * (Nat.stirlingSecond n j : ℚ) / ((j : ℚ) + 1)

-- Auxiliary identity: U(n) = [n = 1]
private lemma kanekoU_eq (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
      * (Nat.stirlingSecond n (j + 1) : ℚ)
      = if n = 1 then 1 else 0 := by
  induction n with
  | zero =>
    simp
  | succ n _ih =>
    have e : ∀ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
          * (Nat.stirlingSecond (n + 1) (j + 1) : ℚ)
        = ((-1 : ℚ) ^ j * (((j + 1).factorial : ℕ) : ℚ) * (Nat.stirlingSecond n (j + 1) : ℚ)
          + (-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond n j : ℚ)) := by
      intro j _
      have hS := Nat.stirlingSecond_succ_succ n j
      rw [hS]
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      ring
    have step : ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
          * (Nat.stirlingSecond (n + 1) (j + 1) : ℚ)
        = (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
            * (Nat.stirlingSecond n (j + 1) : ℚ))
        + (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
            * (Nat.stirlingSecond n j : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl e
    rw [step]
    have hStop : (Nat.stirlingSecond n (n + 1) : ℚ) = 0 := by
      have h : Nat.stirlingSecond n (n + 1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)
      rw [h, Nat.cast_zero]
    have hStopp : (Nat.stirlingSecond n (n + 1 + 1) : ℚ) = 0 := by
      have h : Nat.stirlingSecond n (n + 1 + 1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      rw [h, Nat.cast_zero]
    have hS0 : (Nat.stirlingSecond n 0 : ℚ) = if n = 0 then 1 else 0 := by
      cases n with
      | zero => simp
      | succ n => simp [Nat.stirlingSecond_succ_zero]
    have hQ : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
          * (Nat.stirlingSecond n j : ℚ))
        = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
          * (Nat.stirlingSecond n j : ℚ) := by
      rw [Finset.sum_range_succ]
      have hz : (-1 : ℚ) ^ (n + 1) * (((n + 1).factorial : ℕ) : ℚ)
          * (Nat.stirlingSecond n (n + 1) : ℚ) = 0 := by
        rw [hStop, mul_zero]
      rw [hz, add_zero]
    have hP1 : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n (j + 1) : ℚ))
        = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n (j + 1) : ℚ) := by
      rw [Finset.sum_range_succ]
      have hz : (-1 : ℚ) ^ (n + 1) * (((((n + 1) + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n ((n + 1) + 1) : ℚ) = 0 := by
        have h0 : Nat.stirlingSecond n ((n + 1) + 1) = 0 :=
          Nat.stirlingSecond_eq_zero_of_lt (by omega)
        rw [h0, Nat.cast_zero, mul_zero]
      rw [hz, add_zero]
    have neg : ∀ j : ℕ, (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n (j + 1) : ℚ)
        = -((-1 : ℚ) ^ (j + 1) * ((((j + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n (j + 1) : ℚ)) := by
      intro j
      ring
    have hG1 := Finset.sum_range_succ'
      (fun i => (-1 : ℚ) ^ i * (((i.factorial) : ℕ) : ℚ) * (Nat.stirlingSecond n i : ℚ)) (n + 1)
    have hG2 := Finset.sum_range_succ
      (fun i => (-1 : ℚ) ^ i * (((i.factorial) : ℕ) : ℚ) * (Nat.stirlingSecond n i : ℚ)) (n + 1)
    have hg0 : (-1 : ℚ) ^ (0 : ℕ) * ((((0).factorial) : ℕ) : ℚ)
        * (Nat.stirlingSecond n 0 : ℚ) = (if n = 0 then (1 : ℚ) else 0) := by
      simp [hS0]
    have hgn : (-1 : ℚ) ^ (n + 1) * ((((n + 1).factorial) : ℕ) : ℚ)
        * (Nat.stirlingSecond n (n + 1) : ℚ) = 0 := by
      rw [hStop, mul_zero]
    have hShift : (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (j + 1)
          * ((((j + 1).factorial) : ℕ) : ℚ) * (Nat.stirlingSecond n (j + 1) : ℚ))
        = (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
            * (Nat.stirlingSecond n j : ℚ)) - (if n = 0 then (1 : ℚ) else 0) := by
      have h3 := hG1.symm.trans hG2
      simp only [hg0, hgn, add_zero] at h3
      exact (eq_sub_iff_add_eq).mpr h3
    have hP : (∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
          * (Nat.stirlingSecond n (j + 1) : ℚ))
        = (if n = 0 then (1 : ℚ) else 0) - ∑ j ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond n j : ℚ) := by
      rw [hP1]
      have t1 : (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * ((((j + 1).factorial) : ℕ) : ℚ)
            * (Nat.stirlingSecond n (j + 1) : ℚ))
          = ∑ j ∈ Finset.range (n + 1), -((-1 : ℚ) ^ (j + 1) * ((((j + 1).factorial) : ℕ) : ℚ)
            * (Nat.stirlingSecond n (j + 1) : ℚ)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact neg j
      rw [t1, Finset.sum_neg_distrib, hShift, neg_sub]
    rw [hP, hQ, sub_add_cancel]
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [hn]

-- extend the sum defining kanekoT k to the larger range (n+1)
private lemma kanekoT_extend (n k : ℕ) (hkn : k ≤ n) : kanekoT k
    = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
      * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1) := by
  unfold kanekoT
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkn))
  intro j hj1 hj2
  have hkj : k < j := by
    simp only [Finset.mem_range] at hj1 hj2
    omega
  have hS : Nat.stirlingSecond k j = 0 := Nat.stirlingSecond_eq_zero_of_lt hkj
  rw [hS, Nat.cast_zero, mul_zero, zero_div]

-- partial binomial-Stirling sum
private lemma kanekoT_inner (n j : ℕ) :
    ∑ k ∈ Finset.range n, (n.choose k : ℚ) * (Nat.stirlingSecond k j : ℚ)
      = (Nat.stirlingSecond (n + 1) (j + 1) : ℚ) - (Nat.stirlingSecond n j : ℚ) := by
  have h1 := stirling_binom_full n j
  rw [Finset.sum_range_succ] at h1
  have hc : (n.choose n : ℚ) = 1 := by
    rw [Nat.choose_self, Nat.cast_one]
  rw [hc, one_mul] at h1
  exact (eq_sub_iff_add_eq).mpr h1

-- pointwise Stirling split with the 1/(j+1) weight
private lemma kanekoT_perA (n j : ℕ) :
    (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
      * (Nat.stirlingSecond (n + 1) (j + 1) : ℚ))
    = ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond n (j + 1) : ℚ))
      + (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * (Nat.stirlingSecond n j : ℚ)) := by
  have hS := Nat.stirlingSecond_succ_succ n j
  have hj : ((j : ℚ) + 1) ≠ 0 := by
    have hpos : (0 : ℚ) < (j : ℚ) + 1 := by positivity
    exact ne_of_gt hpos
  rw [hS]
  push_cast
  field_simp

-- the candidate satisfies the Bernoulli recurrence
private lemma kanekoT_rec (n : ℕ) :
    ∑ k ∈ Finset.range n, (n.choose k : ℚ) * kanekoT k
      = if n = 1 then 1 else 0 := by
  have e1 : ∀ k ∈ Finset.range n, (n.choose k : ℚ) * kanekoT k
      = ∑ j ∈ Finset.range (n + 1), (n.choose k : ℚ)
        * ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1)) := by
    intro k hk
    have hkn : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
    rw [kanekoT_extend n k hkn, Finset.mul_sum]
  have swap : (∑ k ∈ Finset.range n, (n.choose k : ℚ) * kanekoT k)
      = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range n, (n.choose k : ℚ)
        * ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1)) :=
    calc (∑ k ∈ Finset.range n, (n.choose k : ℚ) * kanekoT k)
          = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), (n.choose k : ℚ)
            * ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1)) :=
        Finset.sum_congr rfl e1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range n, (n.choose k : ℚ)
            * ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1)) :=
        Finset.sum_comm
  have step2 : (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range n, (n.choose k : ℚ)
        * ((-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond k j : ℚ) / ((j : ℚ) + 1)))
      = ∑ j ∈ Finset.range (n + 1), (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * ∑ k ∈ Finset.range n, (n.choose k : ℚ) * (Nat.stirlingSecond k j : ℚ)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have step2b : (∑ j ∈ Finset.range (n + 1), (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * ∑ k ∈ Finset.range n, (n.choose k : ℚ) * (Nat.stirlingSecond k j : ℚ)))
      = ∑ j ∈ Finset.range (n + 1), (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * ((Nat.stirlingSecond (n + 1) (j + 1) : ℚ) - (Nat.stirlingSecond n j : ℚ))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [kanekoT_inner n j]
  have e3 : ∀ j ∈ Finset.range (n + 1), (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * ((Nat.stirlingSecond (n + 1) (j + 1) : ℚ) - (Nat.stirlingSecond n j : ℚ)))
      = (-1 : ℚ) ^ j * (j.factorial : ℚ) * (Nat.stirlingSecond n (j + 1) : ℚ) := by
    intro j _
    rw [mul_sub, kanekoT_perA n j, add_sub_cancel_right]
  have step3 : (∑ j ∈ Finset.range (n + 1), (((-1 : ℚ) ^ j * (j.factorial : ℚ) / ((j : ℚ) + 1))
        * ((Nat.stirlingSecond (n + 1) (j + 1) : ℚ) - (Nat.stirlingSecond n j : ℚ))))
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
        * (Nat.stirlingSecond n (j + 1) : ℚ) :=
    Finset.sum_congr rfl e3
  rw [swap, step2, step2b, step3]
  exact kanekoU_eq n

-- uniqueness: the candidate equals bernoulli
private lemma kanekoT_eq_bernoulli (n : ℕ) : kanekoT n = bernoulli n := by
  have key : ∀ m, (∀ k, k < m → kanekoT k = bernoulli k) → kanekoT m = bernoulli m := by
    intro m ihm
    have hT := kanekoT_rec (m + 1)
    have hB := sum_bernoulli (m + 1)
    rw [Finset.sum_range_succ] at hT hB
    have hc : ((m + 1).choose m : ℚ) = (m : ℚ) + 1 := by
      rw [Nat.choose_succ_self_right]
      push_cast
      ring
    rw [hc] at hT hB
    have hsum : ∑ k ∈ Finset.range m, ((m + 1).choose k : ℚ) * kanekoT k
        = ∑ k ∈ Finset.range m, ((m + 1).choose k : ℚ) * bernoulli k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ihm k (Finset.mem_range.mp hk)]
    rw [hsum] at hT
    have hpos : (0 : ℚ) < (m : ℚ) + 1 := by positivity
    have hne : (m : ℚ) + 1 ≠ 0 := ne_of_gt hpos
    have heq : ((m : ℚ) + 1) * kanekoT m = ((m : ℚ) + 1) * bernoulli m := by
      linear_combination hT - hB
    exact mul_left_cancel₀ hne heq
  exact Nat.strong_induction_on n key

-- reindex a sum over Icc 1 (n+1) by (m - 1)
private lemma icc_reidx (n : ℕ) (F : ℕ → ℚ) :
    ∑ m ∈ Finset.Icc 1 (n + 1), F (m - 1) = ∑ j ∈ Finset.range (n + 1), F j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Icc 1 (n + 1 + 1) = insert (n + 1 + 1) (Finset.Icc 1 (n + 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h2 : n + 1 + 1 - 1 = n + 1 := by omega
    rw [hI, Finset.sum_insert (by simp), Finset.sum_range_succ, ih, h2]
    exact add_comm _ _

/--
**Kaneko's Stirling-number formula for the Bernoulli numbers.** Let $B_n$ denote the $n$-th
Bernoulli number, with $B_1 = -1/2$, and let $S(n, j)$ denote the Stirling numbers of the second
kind. For every natural number $n$,
$$B_n = \sum_{m=1}^{n+1} \frac{(-1)^{m-1} (m-1)!\, S(n, m-1)}{m}.$$

This is Kaneko's explicit formula for the poly-Bernoulli numbers $B_n^{(k)}$ at $k = 1$. That
formula carries a factor $(-1)^n$, which cancels against $B_n^{(1)} = (-1)^n B_n$ (the numbers
$B_n^{(1)}$ come from the generating series $t/(1 - e^{-t})$).

Proves `Wanted` entry `kaneko_bernoulli_stirling_sum`.

Source: Y. Hamahata and H. Masubuchi,
"Special Multi-Poly-Bernoulli Numbers,"
Journal of Integer Sequences 10 (2007), Article 07.4.1,
Theorem [Kaneko1] (label 1), lines 144–152,
https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex
citing M. Kaneko, "Poly-Bernoulli numbers,"
Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
-/
theorem kaneko_bernoulli_stirling_sum
    (n : ℕ) :
    bernoulli n = ∑ m ∈ Finset.Icc 1 (n + 1),
      (-1 : ℚ) ^ (m - 1) * (Nat.factorial (m - 1) : ℚ) *
        (Nat.stirlingSecond n (m - 1) : ℚ) / (m : ℚ) := by
  rw [← kanekoT_eq_bernoulli n]
  have hF : ∀ m ∈ Finset.Icc 1 (n + 1),
      (-1 : ℚ) ^ (m - 1) * (Nat.factorial (m - 1) : ℚ) *
        (Nat.stirlingSecond n (m - 1) : ℚ) / (m : ℚ)
      = ((-1 : ℚ) ^ (m - 1) * (((m - 1).factorial : ℕ) : ℚ)
        * (Nat.stirlingSecond n (m - 1) : ℚ) / ((((m - 1) + 1 : ℕ)) : ℚ)) := by
    intro m hm
    have h1 : m - 1 + 1 = m := by
      simp only [Finset.mem_Icc] at hm
      omega
    rw [h1]
  have step1 : (∑ m ∈ Finset.Icc 1 (n + 1), (-1 : ℚ) ^ (m - 1)
        * (Nat.factorial (m - 1) : ℚ) * (Nat.stirlingSecond n (m - 1) : ℚ) / (m : ℚ))
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
        * (Nat.stirlingSecond n j : ℚ) / (((j + 1 : ℕ)) : ℚ) := by
    rw [Finset.sum_congr rfl hF]
    exact icc_reidx n (fun j => (-1 : ℚ) ^ j * (j.factorial : ℚ)
      * (Nat.stirlingSecond n j : ℚ) / (((j + 1 : ℕ)) : ℚ))
  have step2 : (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
        * (Nat.stirlingSecond n j : ℚ) / (((j + 1 : ℕ)) : ℚ)) = kanekoT n := by
    unfold kanekoT
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [step1, step2]

end MetaMathlibExt
