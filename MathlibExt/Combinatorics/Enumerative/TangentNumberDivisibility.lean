/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Signed tangent number 2-adic divisibility and mod-6 congruence
-/

private lemma T_one_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k)) :
    T 1 = 1 := by
  have h := hT_succ 0
  simp only [zero_add, ↓reduceIte, Finset.range_one, zero_tsub, Finset.sum_singleton,
      Nat.choose_self, Nat.cast_one, one_mul]at h
  rw [hT_zero] at h
  simpa using h

private lemma T_even_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (N : ℕ) (hN : Even N) : T N = 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N, hN with
    | 0, _ => exact hT_zero
    | m + 1, hN =>
      have hEven : Even (m + 1) := hN
      obtain ⟨t, ht⟩ := hEven
      have hm0 : m ≠ 0 := by omega
      have hT := hT_succ m
      simp only [hm0, ite_false] at hT
      have hsum : ∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℤ) * T k * T (m - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_range] at hk
        have hkm : k ≤ m := by omega
        have hk1 : k < m + 1 := hk
        have hk2 : m - k < m + 1 := by omega
        have hpar : Even k ∨ Even (m - k) := by
          by_contra hc
          push Not at hc
          obtain ⟨hc1, hc2⟩ := hc
          rw [Nat.not_even_iff_odd] at hc1 hc2
          have hadd : Even (k + (m - k)) := hc1.add_odd hc2
          rw [Nat.add_sub_cancel' hkm] at hadd
          obtain ⟨a, ha⟩ := hadd
          omega
        rcases hpar with h | h
        · have hkT : T k = 0 := ih k hk1 h
          rw [hkT, mul_zero, zero_mul]
        · have hkT : T (m - k) = 0 := ih (m - k) hk2 h
          rw [hkT, mul_zero]
      rw [hT, hsum, sub_zero]

private lemma choose_even_aux (n k : ℕ) (_hn : 1 ≤ n) (hkodd : Odd k) (hkle : k ≤ 2 * n) :
    2 ∣ (2 * n).choose k := by
  obtain ⟨j, hj⟩ := hkodd
  have hk_eq : k = (2 * j) + 1 := by omega
  subst hk_eq
  have hle : 2 * j + 1 ≤ 2 * n := hkle
  have key := Nat.choose_succ_right_eq (2 * n) (2 * j)
  obtain ⟨s, hs⟩ : Even (2 * n - 2 * j) := by
    exact ⟨n - j, by omega⟩
  have hs' : (2 * n).choose (2 * j) * (2 * n - 2 * j)
      = 2 * ((2 * n).choose (2 * j) * s) := by rw [hs]; ring
  have h2 : (2 * j + 1) * (2 * n).choose (2 * j + 1)
      = (2 * n).choose (2 * j) * (2 * n - 2 * j) := by
    rw [mul_comm (2 * j + 1) _]
    exact key
  have hdvd : 2 ∣ (2 * j + 1) * (2 * n).choose (2 * j + 1) := by
    rw [h2, hs']
    exact dvd_mul_right 2 _
  rcases (Nat.prime_two.dvd_mul.mp hdvd) with h | h
  · exfalso; omega
  · exact h

private lemma dvd_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) : (2 : ℤ) ^ n ∣ T (2 * n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 1 ≤ n
    · have hTeq : T (2 * n + 1) =
          - ∑ k ∈ Finset.range (2 * n + 1),
            ((2 * n).choose k : ℤ) * T k * T (2 * n - k) := by
        have h := hT_succ (2 * n)
        have h2n : 2 * n ≠ 0 := by omega
        simp only [h2n, ite_false] at h
        have heq : 2 * n + 1 = (2 * n) + 1 := by omega
        rw [heq] at h ⊢
        linarith
      rw [hTeq]
      apply dvd_neg.mpr
      apply Finset.dvd_sum
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases hke : Even k
      · have hkT : T k = 0 :=
          T_even_aux T hT_zero hT_succ k hke
        simp [hkT]
      · rw [Nat.not_even_iff_odd] at hke
        have hkeOdd : Odd k := hke
        obtain ⟨i, hi⟩ := hke
        have hk_eq : k = 2 * i + 1 := by omega
        have hin : i < n := by omega
        have hco : 2 * n - k = 2 * (n - 1 - i) + 1 := by omega
        have hkle : k ≤ 2 * n := by omega
        have hC : (2 : ℤ) ∣ ((2 * n).choose k : ℤ) := by
          have hnat : 2 ∣ (2 * n).choose k :=
            choose_even_aux n k hn hkeOdd hkle
          exact_mod_cast hnat
        have h1 : (2 : ℤ) ^ i ∣ T k := by
          rw [hk_eq]
          exact ih i hin
        have h2 : (2 : ℤ) ^ (n - 1 - i) ∣ T (2 * n - k) := by
          rw [hco]
          have hlt : n - 1 - i < n := by omega
          exact ih (n - 1 - i) hlt
        have e1 : i + (n - 1 - i) = n - 1 := by omega
        have e2 : n - 1 + 1 = n := by omega
        have hpow : (2 : ℤ) ^ n = 2 * ((2 : ℤ) ^ i * (2 : ℤ) ^ (n - 1 - i)) := by
          conv_lhs => rw [← e2, pow_succ]
          rw [← pow_add, e1]
          ring
        rw [hpow]
        have hmul : (2 : ℤ) ^ i * (2 : ℤ) ^ (n - 1 - i) ∣ T k * T (2 * n - k) :=
          mul_dvd_mul h1 h2
        have hshape : (2 : ℤ) * ((2 : ℤ) ^ i * (2 : ℤ) ^ (n - 1 - i)) ∣
            ((2 * n).choose k : ℤ) * (T k * T (2 * n - k)) :=
          mul_dvd_mul hC hmul
        have hrw : ((2 * n).choose k : ℤ) * T k * T (2 * n - k)
            = ((2 * n).choose k : ℤ) * (T k * T (2 * n - k)) := by ring
        rw [hrw]
        exact hshape
    · push Not at hn
      interval_cases n
      simp

private lemma filter_odd_image_aux (n : ℕ) :
    Finset.filter Odd (Finset.range (2 * n + 1))
      = Finset.image (fun i => 2 * i + 1) (Finset.range n) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨hk, hko⟩ := h
    obtain ⟨i, hi⟩ := hko
    have hi2 : k = 2 * i + 1 := by omega
    have hin : i < n := by omega
    exact ⟨i, hin, by omega⟩
  · intro h
    obtain ⟨i, hin, hik⟩ := h
    constructor
    · omega
    · exact ⟨i, by omega⟩

private lemma U_rec_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) (hn : 1 ≤ n) :
    T (2 * n + 1) / (2 : ℤ) ^ n =
      - ∑ i ∈ Finset.range n,
        ((((2 * n).choose (2 * i + 1) : ℕ) : ℤ) / 2)
          * (T (2 * i + 1) / (2 : ℤ) ^ i)
          * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)) := by
  have hTeq : T (2 * n + 1) =
      - ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) * T k * T (2 * n - k) := by
    have h := hT_succ (2 * n)
    have h2n : 2 * n ≠ 0 := by omega
    simp only [h2n, ite_false] at h
    have heq : 2 * n + 1 = (2 * n) + 1 := by omega
    rw [heq] at h ⊢
    linarith
  have hvan : ∀ k ∈ Finset.range (2 * n + 1), ¬ Odd k →
      ((2 * n).choose k : ℤ) * T k * T (2 * n - k) = 0 := by
    intro k hk hno
    have hke : Even k := Nat.not_odd_iff_even.mp hno
    have hkT : T k = 0 := T_even_aux T hT_zero hT_succ k hke
    simp [hkT]
  have hsub : ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) * T k * T (2 * n - k)
      = ∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)),
        ((2 * n).choose k : ℤ) * T k * T (2 * n - k) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnk
    have hno : ¬ Odd k := by
      intro ho
      exact hnk (Finset.mem_filter.mpr ⟨hk, ho⟩)
    exact hvan k hk hno
  have him := filter_odd_image_aux n
  have hinj : Set.InjOn (fun i => 2 * i + 1) (↑(Finset.range n) : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have himg : ∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)),
        ((2 * n).choose k : ℤ) * T k * T (2 * n - k)
      = ∑ i ∈ Finset.range n,
        (((2 * n).choose (2 * i + 1) : ℕ) : ℤ) * T (2 * i + 1) * T (2 * n - (2 * i + 1)) := by
    rw [him, Finset.sum_image hinj]
  have hterm : ∀ i ∈ Finset.range n,
      (((2 * n).choose (2 * i + 1) : ℕ) : ℤ) * T (2 * i + 1) * T (2 * n - (2 * i + 1))
        = (2 : ℤ) ^ n *
          (((((2 * n).choose (2 * i + 1) : ℕ) : ℤ) / 2)
            * (T (2 * i + 1) / (2 : ℤ) ^ i)
            * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hco : 2 * n - (2 * i + 1) = 2 * (n - 1 - i) + 1 := by omega
    have hkle : 2 * i + 1 ≤ 2 * n := by omega
    have hCnat : 2 ∣ (2 * n).choose (2 * i + 1) :=
      choose_even_aux n (2 * i + 1) hn ⟨i, rfl⟩ hkle
    have hC : (2 : ℤ) ∣ ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) := by
      exact_mod_cast hCnat
    have hC2 : 2 * (((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2)
        = ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel hC
    have h1 : (2 : ℤ) ^ i ∣ T (2 * i + 1) := dvd_aux T hT_zero hT_succ i
    have hT1 : (2 : ℤ) ^ i * (T (2 * i + 1) / (2 : ℤ) ^ i) = T (2 * i + 1) := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel h1
    have h2dvd : (2 : ℤ) ^ (n - 1 - i) ∣ T (2 * (n - 1 - i) + 1) :=
      dvd_aux T hT_zero hT_succ (n - 1 - i)
    have hT2 : (2 : ℤ) ^ (n - 1 - i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))
        = T (2 * (n - 1 - i) + 1) := by
      rw [mul_comm]
      exact Int.ediv_mul_cancel h2dvd
    have e1 : i + (n - 1 - i) = n - 1 := by omega
    have e2 : n - 1 + 1 = n := by omega
    have hpow : (2 : ℤ) ^ n = 2 * ((2 : ℤ) ^ i * (2 : ℤ) ^ (n - 1 - i)) := by
      conv_lhs => rw [← e2, pow_succ]
      rw [← pow_add, e1]
      ring
    rw [hco]
    have hreg : (2 : ℤ) ^ n *
          (((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2 *
            (T (2 * i + 1) / (2 : ℤ) ^ i) *
            (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))
        = (2 * (((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2)) *
          (((2 : ℤ) ^ i * (T (2 * i + 1) / (2 : ℤ) ^ i)) *
            ((2 : ℤ) ^ (n - 1 - i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))) := by
      rw [hpow]; ring
    rw [hreg, hC2, hT1, hT2]
    ring
  have hsum_eq : ∑ k ∈ Finset.range (2 * n + 1),
        ((2 * n).choose k : ℤ) * T k * T (2 * n - k)
      = (2 : ℤ) ^ n * ∑ i ∈ Finset.range n,
        (((((2 * n).choose (2 * i + 1) : ℕ) : ℤ) / 2)
          * (T (2 * i + 1) / (2 : ℤ) ^ i)
          * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))) := by
    rw [hsub, himg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  have hT2n : T (2 * n + 1)
      = (2 : ℤ) ^ n *
        (- ∑ i ∈ Finset.range n,
          (((((2 * n).choose (2 * i + 1) : ℕ) : ℤ) / 2)
            * (T (2 * i + 1) / (2 : ℤ) ^ i)
            * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))) := by
    rw [hTeq, hsum_eq]
    ring
  rw [hT2n, mul_comm ((2 : ℤ) ^ n)]
  exact Int.mul_ediv_cancel _ (pow_ne_zero n (show (2 : ℤ) ≠ 0 by norm_num))

private lemma odd_sum_aux (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k
      = 2 ^ (2 * n - 1) := by
  have h2n : 0 < 2 * n := by omega
  have htotal : ∑ m ∈ Finset.range (2 * n + 1), (2 * n).choose m = 2 ^ (2 * n) := by
    have h := Nat.sum_range_choose (2 * n)
    have heq : (2 * n) + 1 = 2 * n + 1 := by omega
    rwa [heq] at h
  have halt : ∑ m ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ m * (((2 * n).choose m : ℕ) : ℤ) = 0 := by
    have hbp := add_pow (-1 : ℤ) (1 : ℤ) (2 * n)
    have h01 : (-1 : ℤ) + 1 = 0 := by norm_num
    have hlhs : ((-1 : ℤ) + 1) ^ (2 * n) = 0 := by
      rw [h01]
      exact zero_pow (by omega : 2 * n ≠ 0)
    rw [hlhs] at hbp
    have hrw : ∀ m ∈ Finset.range (2 * n + 1),
        (-1 : ℤ) ^ m * (1 : ℤ) ^ (2 * n - m) * (((2 * n).choose m : ℕ) : ℤ)
          = (-1 : ℤ) ^ m * (((2 * n).choose m : ℕ) : ℤ) := by
      intro m _
      simp
    rw [Finset.sum_congr rfl hrw] at hbp
    linarith
  have hsplitN : ∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k
      + ∑ k ∈ Finset.filter Even (Finset.range (2 * n + 1)), (2 * n).choose k
      = 2 ^ (2 * n) := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.range (2 * n + 1)) (fun k => Odd k) (fun k => (2 * n).choose k)
    have heq : Finset.filter (fun k => ¬ Odd k) (Finset.range (2 * n + 1))
        = Finset.filter Even (Finset.range (2 * n + 1)) := by
      apply Finset.filter_congr
      intro k _
      rw [Nat.not_odd_iff_even]
    rw [heq] at h
    linarith [h, htotal]
  have hsplitZ : ((∑ k ∈ Finset.filter Even (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ)
      - ((∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ) = 0 := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.range (2 * n + 1)) (fun k => Odd k)
      (fun k => (-1 : ℤ) ^ k * (((2 * n).choose k : ℕ) : ℤ))
    have heq : (∑ x ∈ Finset.filter (fun k => ¬ Odd k) (Finset.range (2 * n + 1)),
          (-1 : ℤ) ^ x * (((2 * n).choose x : ℕ) : ℤ))
        = ((∑ k ∈ Finset.filter Even (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ) := by
      have hcongr : Finset.filter (fun k => ¬ Odd k) (Finset.range (2 * n + 1))
          = Finset.filter Even (Finset.range (2 * n + 1)) := by
        apply Finset.filter_congr
        intro k _
        rw [Nat.not_odd_iff_even]
      rw [hcongr]
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨_, hke⟩ := hk
      rw [hke.neg_one_pow]
      simp
    have heq2 : (∑ x ∈ Finset.filter (fun k => Odd k) (Finset.range (2 * n + 1)),
          (-1 : ℤ) ^ x * (((2 * n).choose x : ℕ) : ℤ))
        = - ((∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ) := by
      rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨_, hko⟩ := hk
      rw [hko.neg_one_pow]
      simp
    rw [heq, heq2] at h
    linarith [h, halt]
  have hcast : ((∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ)
      + ((∑ k ∈ Finset.filter Even (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) : ℤ)
      = ((2 ^ (2 * n) : ℕ) : ℤ) := by
    exact_mod_cast hsplitN
  have h2 : (2 : ℤ) * ((∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k : ℕ) :
      ℤ)
      = (2 : ℤ) * ((2 ^ (2 * n - 1) : ℕ) : ℤ) := by
    have hpow : (2 : ℤ) ^ (2 * n) = 2 * ((2 ^ (2 * n - 1) : ℕ) : ℤ) := by
      have e : 2 * n - 1 + 1 = 2 * n := by omega
      conv_lhs => rw [← e, pow_succ]
      simp [mul_comm]
    have hcast2 : ((2 ^ (2 * n) : ℕ) : ℤ) = (2 : ℤ) ^ (2 * n) := by
      exact_mod_cast rfl
    linarith [hcast, hsplitZ, hpow, hcast2]
  have hnat : 2 * (∑ k ∈ Finset.filter Odd (Finset.range (2 * n + 1)), (2 * n).choose k)
      = 2 * (2 ^ (2 * n - 1)) := by
    exact_mod_cast h2
  have := Nat.mul_left_cancel (by norm_num : 0 < 2) hnat
  exact this

private lemma T_three_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k)) :
    T 3 = -2 := by
  have hT1 := T_one_aux T hT_zero hT_succ
  have hT2 := T_even_aux T hT_zero hT_succ 2 ⟨1, rfl⟩
  have h := hT_succ 2
  have h20 : (2 : ℕ) ≠ 0 := by decide
  simp only [h20, ite_false] at h
  have e : (2 : ℕ) + 1 = 3 := rfl
  rw [e] at h
  rw [h]
  have c0 : (2 : ℕ).choose 0 = 1 := by decide
  have c1 : (2 : ℕ).choose 1 = 2 := by decide
  have c2 : (2 : ℕ).choose 2 = 1 := by decide
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  rw [c0, c1, c2, hT_zero, hT1, hT2]
  norm_num

private lemma T_five_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k)) :
    T 5 = 16 := by
  have hT1 := T_one_aux T hT_zero hT_succ
  have hT2 := T_even_aux T hT_zero hT_succ 2 ⟨1, rfl⟩
  have hT3 := T_three_aux T hT_zero hT_succ
  have hT4 := T_even_aux T hT_zero hT_succ 4 ⟨2, rfl⟩
  have h := hT_succ 4
  have h40 : (4 : ℕ) ≠ 0 := by decide
  simp only [h40, ite_false] at h
  have e : (4 : ℕ) + 1 = 5 := rfl
  rw [e] at h
  rw [h]
  have c0 : (4 : ℕ).choose 0 = 1 := by decide
  have c1 : (4 : ℕ).choose 1 = 4 := by decide
  have c2 : (4 : ℕ).choose 2 = 6 := by decide
  have c3 : (4 : ℕ).choose 3 = 4 := by decide
  have c4 : (4 : ℕ).choose 4 = 1 := by decide
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [c0, c1, c2, c3, c4, hT_zero, hT1, hT2, hT3, hT4]
  norm_num

private lemma T_seven_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k)) :
    T 7 = -272 := by
  have hT1 := T_one_aux T hT_zero hT_succ
  have hT2 := T_even_aux T hT_zero hT_succ 2 ⟨1, rfl⟩
  have hT3 := T_three_aux T hT_zero hT_succ
  have hT4 := T_even_aux T hT_zero hT_succ 4 ⟨2, rfl⟩
  have hT5 := T_five_aux T hT_zero hT_succ
  have hT6 := T_even_aux T hT_zero hT_succ 6 ⟨3, rfl⟩
  have h := hT_succ 6
  have h60 : (6 : ℕ) ≠ 0 := by decide
  simp only [h60, ite_false] at h
  have e : (6 : ℕ) + 1 = 7 := rfl
  rw [e] at h
  rw [h]
  have c0 : (6 : ℕ).choose 0 = 1 := by decide
  have c1 : (6 : ℕ).choose 1 = 6 := by decide
  have c2 : (6 : ℕ).choose 2 = 15 := by decide
  have c3 : (6 : ℕ).choose 3 = 20 := by decide
  have c4 : (6 : ℕ).choose 4 = 15 := by decide
  have c5 : (6 : ℕ).choose 5 = 6 := by decide
  have c6 : (6 : ℕ).choose 6 = 1 := by decide
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  rw [c0, c1, c2, c3, c4, c5, c6, hT_zero, hT1, hT2, hT3, hT4, hT5, hT6]
  norm_num

private lemma twoU_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) (hn : 1 ≤ n) :
    2 * (T (2 * n + 1) / (2 : ℤ) ^ n) =
      - ∑ i ∈ Finset.range n,
        ((((2 * n).choose (2 * i + 1) : ℕ) : ℤ))
          * (T (2 * i + 1) / (2 : ℤ) ^ i)
          * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)) := by
  rw [U_rec_aux T hT_zero hT_succ n hn, mul_neg, Finset.mul_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hkle : 2 * i + 1 ≤ 2 * n := by omega
  have hCnat : 2 ∣ (2 * n).choose (2 * i + 1) :=
    choose_even_aux n (2 * i + 1) hn ⟨i, rfl⟩ hkle
  have hC : (2 : ℤ) ∣ ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) := by
    exact_mod_cast hCnat
  have hC2 : 2 * (((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2)
      = ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hC
  calc 2 * ((((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2)
        * (T (2 * i + 1) / (2 : ℤ) ^ i)
        * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))
      = (2 * (((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) / 2))
        * ((T (2 * i + 1) / (2 : ℤ) ^ i)
          * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))) := by ring
    _ = ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ)
        * ((T (2 * i + 1) / (2 : ℤ) ^ i)
          * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))) := by rw [hC2]
    _ = ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ)
        * (T (2 * i + 1) / (2 : ℤ) ^ i)
        * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)) := by ring

private lemma Csum_aux (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, (2 * n).choose (2 * i + 1) = 2 ^ (2 * n - 1) := by
  have h := odd_sum_aux n hn
  have hinj : Set.InjOn (fun i => 2 * i + 1) (↑(Finset.range n) : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    omega
  rw [filter_odd_image_aux n, Finset.sum_image hinj] at h
  exact h

private lemma cancel_two_mod_three_aux (a b : ℤ)
    (h : Int.ModEq 3 (2 * a) (2 * b)) : Int.ModEq 3 a b := by
  have h2 := Int.ModEq.mul_left 2 h
  have e1 : (2 : ℤ) * (2 * a) = 4 * a := by ring
  have e2 : (2 : ℤ) * (2 * b) = 4 * b := by ring
  rw [e1, e2] at h2
  have h4 : Int.ModEq 3 (4 : ℤ) 1 := by decide
  have g1 : Int.ModEq 3 ((4 : ℤ) * a) (1 * a) := Int.ModEq.mul_right a h4
  have g2 : Int.ModEq 3 ((4 : ℤ) * b) (1 * b) := Int.ModEq.mul_right b h4
  rw [one_mul] at g1 g2
  exact g1.symm.trans (h2.trans g2)

private lemma mod3_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) (hn : 1 ≤ n) :
    Int.ModEq 3 (T (2 * n + 1) / (2 : ℤ) ^ n) ((-1 : ℤ) ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hU0 : T (2 * 0 + 1) / (2 : ℤ) ^ 0 = 1 := by
      have e1 : (2 : ℕ) * 0 + 1 = 1 := rfl
      rw [e1, pow_zero, Int.ediv_one]
      exact T_one_aux T hT_zero hT_succ
    have hU0mod : Int.ModEq 3 (T (2 * 0 + 1) / (2 : ℤ) ^ 0) ((-1 : ℤ) ^ 0) := by
      rw [hU0, pow_zero]
    have hmem : ∀ i < n, Int.ModEq 3 (T (2 * i + 1) / (2 : ℤ) ^ i) ((-1 : ℤ) ^ i) := by
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        exact hU0mod
      · have hi1 : 1 ≤ i := by omega
        exact ih i hi hi1
    have h2U := twoU_aux T hT_zero hT_succ n hn
    have hCsum := Csum_aux n hn
    have hS : (3 : ℤ) ∣
        ((∑ i ∈ Finset.range n,
            ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ)
              * (T (2 * i + 1) / (2 : ℤ) ^ i)
              * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))
          - ∑ i ∈ Finset.range n,
            ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) * (-1 : ℤ) ^ (n - 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro i hi
      rw [Finset.mem_range] at hi
      have hij : i + (n - 1 - i) = n - 1 := by omega
      have hprod : Int.ModEq 3
          ((T (2 * i + 1) / (2 : ℤ) ^ i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))
          ((-1 : ℤ) ^ (n - 1)) := by
        have h1 := hmem i hi
        have h2m : n - 1 - i < n := by omega
        have h2 := hmem (n - 1 - i) h2m
        have hm := Int.ModEq.mul h1 h2
        have e : (-1 : ℤ) ^ i * (-1 : ℤ) ^ (n - 1 - i) = (-1 : ℤ) ^ (n - 1) := by
          rw [← pow_add, hij]
        rwa [e] at hm
      have hdvd : (3 : ℤ) ∣
          ((T (2 * i + 1) / (2 : ℤ) ^ i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))
            - (-1 : ℤ) ^ (n - 1)) :=
        Int.modEq_iff_dvd.mp hprod.symm
      have hmul : (3 : ℤ) ∣ ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) *
          ((T (2 * i + 1) / (2 : ℤ) ^ i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))
            - (-1 : ℤ) ^ (n - 1)) :=
        Dvd.dvd.mul_left hdvd _
      have heq : ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ)
            * (T (2 * i + 1) / (2 : ℤ) ^ i)
            * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))
            - ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) * (-1 : ℤ) ^ (n - 1)
          = ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) *
            ((T (2 * i + 1) / (2 : ℤ) ^ i) * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i))
              - (-1 : ℤ) ^ (n - 1)) := by ring
      rwa [heq]
    have hS0 : (∑ i ∈ Finset.range n,
          ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) * (-1 : ℤ) ^ (n - 1))
        = (-1 : ℤ) ^ (n - 1) * (2 : ℤ) ^ (2 * n - 1) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, hCsum]
      push_cast
      ring
    have hneg : (-1 : ℤ) ^ n = -(-1 : ℤ) ^ (n - 1) := by
      have e : n - 1 + 1 = n := by omega
      conv_lhs => rw [← e]
      rw [pow_succ]
      ring
    have h2pow : Int.ModEq 3 ((2 : ℤ) ^ (2 * n - 1)) 2 := by
      have e : 2 * n - 1 = 1 + 2 * (n - 1) := by omega
      have h41 : Int.ModEq 3 (4 : ℤ) 1 := by decide
      have h4p := Int.ModEq.pow (n - 1) h41
      rw [one_pow] at h4p
      have h4p2 := Int.ModEq.mul_left (2 : ℤ) h4p
      have hexact : (2 : ℤ) ^ (2 * n - 1) = 2 * (4 : ℤ) ^ (n - 1) := by
        conv_lhs => rw [e, pow_add, pow_one, pow_mul]
        have h42 : (2 : ℤ) ^ 2 = 4 := by norm_num
        rw [h42]
      rw [hexact]
      simpa using h4p2
    have hd2 : (3 : ℤ) ∣ ((2 : ℤ) ^ (2 * n - 1) - 2) :=
      Int.modEq_iff_dvd.mp h2pow.symm
    have hfin_dvd : (3 : ℤ) ∣
        (2 * ((-1 : ℤ) ^ n) - 2 * (T (2 * n + 1) / (2 : ℤ) ^ n)) := by
      have heq : (2 : ℤ) * ((-1 : ℤ) ^ n) - 2 * (T (2 * n + 1) / (2 : ℤ) ^ n)
          = ((∑ i ∈ Finset.range n,
              ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ)
                * (T (2 * i + 1) / (2 : ℤ) ^ i)
                * (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)))
            - ∑ i ∈ Finset.range n,
              ((((2 * n).choose (2 * i + 1) : ℕ)) : ℤ) * (-1 : ℤ) ^ (n - 1))
            + (-1 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ (2 * n - 1) - 2) := by
        rw [h2U, hS0, hneg]
        ring
      rw [heq]
      exact dvd_add hS (dvd_mul_of_dvd_right hd2 _)
    have hfin : Int.ModEq 3 (2 * (T (2 * n + 1) / (2 : ℤ) ^ n)) (2 * ((-1 : ℤ) ^ n)) :=
      Int.modEq_iff_dvd.mpr hfin_dvd
    exact cancel_two_mod_three_aux _ _ hfin

private lemma mod2_aux (T : ℕ → ℤ) (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ, T (m + 1) =
      (if m = 0 then 1 else 0) -
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) (hn : 2 ≤ n) : (2 : ℤ) ∣ (T (2 * n + 1) / (2 : ℤ) ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h2 : n = 2
    · subst h2
      have hU2 : T (2 * 2 + 1) / (2 : ℤ) ^ 2 = 4 := by
        have e : (2 : ℕ) * 2 + 1 = 5 := rfl
        have hT5 := T_five_aux T hT_zero hT_succ
        rw [e, hT5]
        norm_num
      rw [hU2]
      norm_num
    · by_cases h3 : n = 3
      · subst h3
        have hU3 : T (2 * 3 + 1) / (2 : ℤ) ^ 3 = -34 := by
          have e : (2 : ℕ) * 3 + 1 = 7 := rfl
          have hT7 := T_seven_aux T hT_zero hT_succ
          rw [e, hT7]
          norm_num
        rw [hU3]
        norm_num
      · have hn4 : 4 ≤ n := by omega
        have hn1 : 1 ≤ n := by omega
        rw [U_rec_aux T hT_zero hT_succ n hn1]
        apply dvd_neg.mpr
        apply Finset.dvd_sum
        intro i hi
        rw [Finset.mem_range] at hi
        by_cases h2i : 2 ≤ i
        · have hUi : (2 : ℤ) ∣ (T (2 * i + 1) / (2 : ℤ) ^ i) := ih i hi h2i
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hUi _) _
        · push Not at h2i
          have hji : 2 ≤ n - 1 - i := by omega
          have hjn : n - 1 - i < n := by omega
          have hUj : (2 : ℤ) ∣ (T (2 * (n - 1 - i) + 1) / (2 : ℤ) ^ (n - 1 - i)) :=
            ih (n - 1 - i) hjn hji
          exact dvd_mul_of_dvd_right hUj _

/--
**Tangent numbers: 2-adic divisibility and a congruence mod 6.** Let $T \colon \mathbb{N} \to
\mathbb{Z}$ satisfy $T(0) = 0$ and, for every $m \in \mathbb{N}$,
$$T(m+1) = [m = 0] - \sum_{k=0}^{m} \binom{m}{k} T(k)\, T(m-k),$$
where $[m = 0]$ is $1$ if $m = 0$ and $0$ otherwise. Then for every $n \ge 1$, $2^n$ divides
$T(2n+1)$ and $T(2n+1)/2^n \equiv (-1)^n 4^{n-1} \pmod 6$.

These conditions determine $T$: its values are the coefficients of the exponential generating
function of $\tanh x$, the signed tangent numbers (unsigned, OEIS A009006). The source defines
the tangent numbers through $1 + \tanh x$, which agrees with this recurrence at odd indices.

Proves `Wanted` entry `tangentNumber_two_adic_divisibility_mod_six`.

Source: Kwang-Wu Chen, "An Interesting Lemma for Regular C-fractions,"
Journal of Integer Sequences 6 (2003), Article 03.4.8, Theorem (label
`thm.4`), equation (label `eq.38`), lines 362–369 (tangent numbers defined
at lines 351–360),
https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen53.tex
-/
theorem tangentNumber_two_adic_divisibility_mod_six
    (T : ℕ → ℤ)
    (hT_zero : T 0 = 0)
    (hT_succ : ∀ m : ℕ,
      T (m + 1) =
        (if m = 0 then 1 else 0) -
          ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
    (n : ℕ) (hn : 1 ≤ n) :
    ((2 : ℤ) ^ n ∣ T (2 * n + 1)) ∧
      Int.ModEq 6 (T (2 * n + 1) / (2 : ℤ) ^ n)
        ((-1 : ℤ) ^ n * 4 ^ (n - 1)) := by
  refine ⟨dvd_aux T hT_zero hT_succ n, ?_⟩
  by_cases hn2 : 2 ≤ n
  · have hU2 : (2 : ℤ) ∣ (T (2 * n + 1) / (2 : ℤ) ^ n) :=
      mod2_aux T hT_zero hT_succ n hn2
    have hV2 : (2 : ℤ) ∣ ((-1 : ℤ) ^ n * 4 ^ (n - 1)) := by
      have h42 : (2 : ℤ) ∣ (4 : ℤ) ^ (n - 1) := by
        have e2 : n - 1 = (n - 2) + 1 := by omega
        rw [e2, pow_succ]
        exact dvd_mul_of_dvd_right (by norm_num) _
      exact dvd_mul_of_dvd_right h42 _
    have hmod2 : Int.ModEq 2 (T (2 * n + 1) / (2 : ℤ) ^ n)
        ((-1 : ℤ) ^ n * 4 ^ (n - 1)) := by
      have eU := Int.modEq_zero_iff_dvd.mpr hU2
      have eV := Int.modEq_zero_iff_dvd.mpr hV2
      exact eU.trans eV.symm
    have hmod3U := mod3_aux T hT_zero hT_succ n hn
    have h43 : Int.ModEq 3 ((4 : ℤ) ^ (n - 1)) 1 := by
      have h41 : Int.ModEq 3 (4 : ℤ) 1 := by decide
      have h4p := Int.ModEq.pow (n - 1) h41
      rwa [one_pow] at h4p
    have hmod3 : Int.ModEq 3 (T (2 * n + 1) / (2 : ℤ) ^ n)
        ((-1 : ℤ) ^ n * 4 ^ (n - 1)) := by
      have hV : Int.ModEq 3 ((-1 : ℤ) ^ n * 4 ^ (n - 1)) ((-1 : ℤ) ^ n * 1) :=
        Int.ModEq.mul_left ((-1 : ℤ) ^ n) h43
      rw [mul_one] at hV
      exact hmod3U.trans hV.symm
    have hcop : Nat.Coprime (2 : ℤ).natAbs (3 : ℤ).natAbs := by decide
    have hcombo := (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmod2, hmod3⟩
    have h6 : (2 : ℤ) * 3 = 6 := by norm_num
    rw [h6] at hcombo
    exact hcombo
  · push Not at hn2
    have hn1 : n = 1 := by omega
    subst hn1
    have hU1 : T (2 * 1 + 1) / (2 : ℤ) ^ 1 = -1 := by
      have e : (2 : ℕ) * 1 + 1 = 3 := rfl
      have hT3 := T_three_aux T hT_zero hT_succ
      rw [e, hT3, pow_one]
      norm_num
    have hV1 : (-1 : ℤ) ^ 1 * 4 ^ (1 - 1) = -1 := by norm_num
    rw [hU1, hV1]

end MetaMathlibExt
