/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.NumberTheory.TribonacciPadicValInt
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# The Brocard–Ramanujan equation has no Tribonacci solutions

This module proves that $m! + 1$ is never the square of a Tribonacci number.
The proof uses the $47$-adic valuation of the two-sided Tribonacci sequence
near $\pm 1$ to bound $m$, and finishes with a finite check over the
remaining values of $m$.
-/

namespace MetaMathlibExt

namespace brocardRamanujan_not_tribonacci

private theorem trib_rec (n : ℕ) :
    tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl

private theorem trib_mono_triple : ∀ n : ℕ,
    tribonacci n ≤ tribonacci (n + 1) ∧ tribonacci (n + 1) ≤ tribonacci (n + 2) ∧
      tribonacci (n + 2) ≤ tribonacci (n + 3) := by
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have h4 : tribonacci (n + 4) =
        tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1) := by
      simpa only [show n + 1 + 3 = n + 4 by omega, show n + 1 + 2 = n + 3 by omega,
        show n + 1 + 1 = n + 2 by omega] using trib_rec (n + 1)
    have e : n + 1 + 2 = n + 3 := by omega
    have e2 : n + 1 + 3 = n + 4 := by omega
    rw [e, e2, h4]
    omega

private theorem trib_mono {a b : ℕ} (h : a ≤ b) : tribonacci a ≤ tribonacci b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (trib_mono_triple n).1

/-- Lower bound for the 47-adic valuation of a factorial. -/
private theorem factorial_factorization_lower (m : ℕ) :
    m / 47 ≤ (Nat.factorial m).factorization 47 := by
  by_cases hm : m < 47
  · simp [Nat.div_eq_of_lt hm]
  · have hp47 : Nat.Prime 47 := by decide
    have hb : Nat.log 47 m < Nat.log 47 m + 2 := by omega
    rw [Nat.factorization_factorial hp47 hb]
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log 47 m + 2) := by
      rw [Finset.mem_Ico]; omega
    have hle := Finset.single_le_sum (f := fun i => m / 47 ^ i)
      (fun i _ => Nat.zero_le _) hmem
    simpa using hle

/-- The 47-adic valuation of `m!` is either zero or comes from a lifted class. -/
private theorem valuation_cases {m n : ℕ} (hn : 1 ≤ n)
    (h : Nat.factorial m + 1 = tribonacci n ^ 2) :
    (Nat.factorial m).factorization 47 = 0 ∨
      ∃ r : ℤ, (Nat.factorial m).factorization 47 = 1 + padicValInt 47 r ∧
        47 ^ padicValInt 47 r ≤ r.natAbs ∧ 46 * r.natAbs ≤ (n - 1) + 7 := by
  obtain ⟨hJ1, hval, hother⟩ := tribonacci_padicValInt_fortySeven
  have hfact47 : Fact (Nat.Prime 47) := ⟨by decide⟩
  set k : ℕ := n - 1 with hk_def
  have hnk : n = k + 1 := by omega
  have hQ : tribonacciInt (k : ℤ) = (tribonacci n : ℤ) := by
    rw [hnk, tribonacciInt_nat_eq]
  have hQ2 : ((tribonacci n : ℤ)) ^ 2 - 1 = ((Nat.factorial m : ℕ) : ℤ) := by
    have hcast : ((Nat.factorial m + 1 : ℕ) : ℤ) = ((tribonacci n : ℤ)) ^ 2 := by
      exact_mod_cast h
    push_cast at hcast
    omega
  by_cases hcase : ∃ j ∈ ({1, 2, -2, -3, -7} : Finset ℤ), ∃ r : ℤ, (k : ℤ) = 46 * r + j
  · obtain ⟨j, hj, r, hr⟩ := hcase
    have hjv := hJ1 j hj
    have hr0 : r ≠ 0 := by
      rintro rfl
      have hkj : tribonacciInt (k : ℤ) = tribonacciInt j := by rw [hr]; simp
      rw [hQ] at hkj
      rcases hjv with hjv | hjv
      · have h1 : tribonacci n = 1 := by exact_mod_cast (hkj.trans hjv)
        have h1' : tribonacci n ^ 2 = 1 := by rw [h1]; norm_num
        have hpos := Nat.factorial_pos m
        omega
      · have hnn : (0 : ℤ) ≤ (tribonacci n : ℤ) := by exact_mod_cast Nat.zero_le _
        have hneg : (tribonacci n : ℤ) = -1 := hkj.trans hjv
        omega
    have hvalr := hval j hj r hr0
    have hvalr := hval j hj r hr0
    rw [← hr, hQ] at hvalr
    have hqc2 : tribonacciInt j ^ 2 = 1 := by rcases hjv with hjv | hjv <;> rw [hjv] <;> norm_num
    have hne1 : (tribonacci n : ℤ) - tribonacciInt j ≠ 0 := by
      intro hz
      have hQeq : (tribonacci n : ℤ) = tribonacciInt j := sub_eq_zero.mp hz
      have hzero : ((tribonacci n : ℤ)) ^ 2 - 1 = 0 := by rw [hQeq, hqc2]; norm_num
      rw [hzero] at hQ2
      have h0 : Nat.factorial m = 0 := by exact_mod_cast hQ2.symm
      exact (Nat.factorial_pos m).ne' h0
    have hne2 : (tribonacci n : ℤ) + tribonacciInt j ≠ 0 := by
      intro hz
      have hQeq : (tribonacci n : ℤ) = -tribonacciInt j := eq_neg_of_add_eq_zero_left hz
      have hzero : ((tribonacci n : ℤ)) ^ 2 - 1 = 0 := by rw [hQeq, neg_sq, hqc2]; norm_num
      rw [hzero] at hQ2
      have h0 : Nat.factorial m = 0 := by exact_mod_cast hQ2.symm
      exact (Nat.factorial_pos m).ne' h0
    have hnotdvd2 : ¬ (47 : ℤ) ∣ (tribonacci n : ℤ) + tribonacciInt j := by
      intro hdvd
      have hdvd1 : (47 : ℤ) ∣ (tribonacci n : ℤ) - tribonacciInt j := by
        have hd := padicValInt_dvd (p := 47) ((tribonacci n : ℤ) - tribonacciInt j)
        rw [hvalr] at hd
        exact dvd_trans (dvd_pow_self 47 (by omega : 1 + padicValInt 47 r ≠ 0)) hd
      have hdvd2 : (47 : ℤ) ∣ 2 * tribonacciInt j := by
        have heq : (2 : ℤ) * tribonacciInt j = ((tribonacci n : ℤ) + tribonacciInt j) -
            ((tribonacci n : ℤ) - tribonacciInt j) := by ring
        rw [heq]
        exact dvd_sub hdvd hdvd1
      rcases hjv with hjv | hjv
      · rw [hjv] at hdvd2
        norm_num at hdvd2
      · rw [hjv] at hdvd2
        have hdvd2' : (47 : ℤ) ∣ (2 : ℤ) := by
          have : (2 : ℤ) = -(2 * (-1 : ℤ)) := by norm_num
          rw [this]
          exact dvd_neg.mpr hdvd2
        norm_num at hdvd2'
    have hfac : padicValInt 47 (((tribonacci n : ℤ)) ^ 2 - 1) =
        padicValInt 47 ((tribonacci n : ℤ) - tribonacciInt j) +
          padicValInt 47 ((tribonacci n : ℤ) + tribonacciInt j) := by
      have hprod : ((tribonacci n : ℤ)) ^ 2 - 1 =
          ((tribonacci n : ℤ) - tribonacciInt j) * ((tribonacci n : ℤ) + tribonacciInt j) := by
        linear_combination hqc2
      rw [hprod, padicValInt.mul hne1 hne2]
    rw [padicValInt.eq_zero_of_not_dvd hnotdvd2, hvalr] at hfac
    simp only [add_zero] at hfac
    have hcast : padicValInt 47 (((tribonacci n : ℤ)) ^ 2 - 1) =
        (Nat.factorial m).factorization 47 := by
      rw [hQ2, padicValInt.of_nat, ← Nat.factorization_def _ (by decide : Nat.Prime 47)]
    rw [hcast] at hfac
    right
    refine ⟨r, hfac, ?_, ?_⟩
    · have hdvd := padicValInt_dvd (p := 47) r
      have hnat : (47 : ℕ) ^ padicValInt 47 r ∣ r.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr hdvd
        rwa [Int.natAbs_pow, Int.natAbs_natCast] at h
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hr0) hnat
    · have hjb : -7 ≤ j ∧ j ≤ 2 := by
        fin_cases hj <;> norm_num
      have hRz : (r.natAbs : ℤ) = r ∨ (r.natAbs : ℤ) = -r := by
        by_cases hrge : (0 : ℤ) ≤ r
        · left
          exact Int.natAbs_of_nonneg hrge
        · right
          have hrlt : r < 0 := lt_of_not_ge hrge
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -r by omega)]
      have hbound : ((46 * r.natAbs : ℕ) : ℤ) ≤ (k : ℤ) + 7 := by
        rcases hRz with hRz | hRz <;>
          rw [Nat.cast_mul, Nat.cast_ofNat, hRz] <;> omega
      have hNat : 46 * r.natAbs ≤ k + 7 := by exact_mod_cast hbound
      omega
  · left
    have hnot := hother (k : ℤ) (by
      intro j hj r
      by_contra hcon
      exact hcase ⟨j, hj, r, hcon⟩)
    rw [hQ] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have hndvd : ¬ (47 : ℤ) ∣ ((tribonacci n : ℤ)) ^ 2 - 1 := by
      intro hdvd
      have hprod : ((tribonacci n : ℤ) - 1) * ((tribonacci n : ℤ) + 1) =
          ((tribonacci n : ℤ)) ^ 2 - 1 := by ring
      rw [← hprod] at hdvd
      have hprime : Prime (47 : ℤ) := Nat.prime_iff_prime_int.mp hfact47.out
      rcases (hprime.dvd_or_dvd hdvd) with hd | hd
      · exact h1 hd
      · exact h2 hd
    have hndvdN : ¬ (47 : ℕ) ∣ Nat.factorial m := by
      intro hdvdN
      apply hndvd
      rw [hQ2]
      exact_mod_cast hdvdN
    by_contra hcon
    have hpos : 0 < (Nat.factorial m).factorization 47 := Nat.pos_of_ne_zero hcon
    have hdvd47 : (47 : ℕ) ^ 1 ∣ Nat.factorial m :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 47)
        (Nat.factorial_pos m).ne').mpr (by omega)
    simpa using hndvdN hdvd47


private theorem trib_ge_five (n : ℕ) : 5 * tribonacci n ≤ tribonacci (n + 4) := by
  have h4 : tribonacci (n + 4) =
      tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1) := by
    simpa only [show n + 1 + 3 = n + 4 by omega, show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 1 = n + 2 by omega] using trib_rec (n + 1)
  have h3 : 3 * tribonacci n ≤ tribonacci (n + 3) := by
    rw [trib_rec n]
    have h1 : tribonacci n ≤ tribonacci (n + 1) := (trib_mono_triple n).1
    have h2 : tribonacci n ≤ tribonacci (n + 2) :=
      le_trans (trib_mono_triple n).1 (trib_mono_triple n).2.1
    omega
  have h1 : tribonacci n ≤ tribonacci (n + 1) := (trib_mono_triple n).1
  have h2 : tribonacci n ≤ tribonacci (n + 2) :=
    le_trans (trib_mono_triple n).1 (trib_mono_triple n).2.1
  rw [h4]; omega

private theorem trib_ge_five_pow (k : ℕ) : 5 ^ k ≤ tribonacci (4 * k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 4 * (k + 1) + 2 = (4 * k + 2) + 4 := by omega
    rw [h1]
    have h2 := trib_ge_five (4 * k + 2)
    calc 5 ^ (k + 1) = 5 * 5 ^ k := by rw [pow_succ']
      _ ≤ 5 * tribonacci (4 * k + 2) := Nat.mul_le_mul_left 5 ih
      _ ≤ tribonacci (4 * k + 2 + 4) := h2

private theorem factorial_le_two_pow_sq (m : ℕ) : Nat.factorial m ≤ (2 : ℕ) ^ (m * m) := by
  calc Nat.factorial m ≤ m ^ m := Nat.factorial_le_pow m
    _ ≤ (2 ^ m) ^ m := Nat.pow_le_pow_left (by have := Nat.lt_two_pow_self (n := m); omega) m
    _ = (2 : ℕ) ^ (m * m) := by rw [← pow_mul]

private theorem decomp (n : ℕ) (hn : 2 ≤ n) :
    ∃ t s : ℕ, s < 4 ∧ n = 4 * t + 2 + s :=
  ⟨(n - 2) / 4, (n - 2) % 4, Nat.mod_lt _ (by norm_num), by omega⟩

private theorem index_le_of_eq {m n : ℕ} (hn : 2 ≤ n)
    (h : Nat.factorial m + 1 = tribonacci n ^ 2) : n ≤ m * m + 6 := by
  obtain ⟨t, s, hs, hns⟩ := decomp n hn
  have h5 : 5 ^ t ≤ tribonacci (4 * t + 2) := trib_ge_five_pow t
  have hmono : tribonacci (4 * t + 2) ≤ tribonacci n := trib_mono (by omega)
  have h25 : (25 : ℕ) ^ t ≤ 2 ^ (m * m + 1) := by
    have hsq : (5 ^ t) ^ 2 ≤ tribonacci n ^ 2 :=
      Nat.pow_le_pow_left (le_trans h5 hmono) 2
    have h25t : (25 : ℕ) ^ t = (5 ^ t) ^ 2 := by
      rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [h25t]
    calc (5 ^ t) ^ 2 ≤ tribonacci n ^ 2 := hsq
      _ = Nat.factorial m + 1 := h.symm
      _ ≤ (2 : ℕ) ^ (m * m) + 1 := by
          have hf := factorial_le_two_pow_sq m
          omega
      _ ≤ (2 : ℕ) ^ (m * m + 1) := by
          have hpos : (0 : ℕ) < (2 : ℕ) ^ (m * m) := pow_pos (by norm_num) _
          rw [pow_succ']
          omega
  have h4t : 4 * t ≤ m * m + 1 := by
    by_contra hcon
    have hge : m * m + 2 ≤ 4 * t := by omega
    have hA : (25 : ℕ) ^ (m * m + 2) ≤ (25 : ℕ) ^ (4 * t) :=
      Nat.pow_le_pow_right (by norm_num) hge
    have hB : (25 : ℕ) ^ (4 * t) ≤ (2 : ℕ) ^ (4 * (m * m + 1)) := by
      have h1 : (25 : ℕ) ^ (4 * t) = ((25 : ℕ) ^ t) ^ 4 := by rw [← pow_mul]; congr 1; ring
      have h2 : (2 : ℕ) ^ (4 * (m * m + 1)) = ((2 : ℕ) ^ (m * m + 1)) ^ 4 := by
        rw [← pow_mul]; congr 1; ring
      rw [h1, h2]
      exact Nat.pow_le_pow_left h25 4
    have hC : (2 : ℕ) ^ (4 * (m * m + 1)) < (25 : ℕ) ^ (m * m + 2) := by
      have e1 : (2 : ℕ) ^ (4 * (m * m + 1)) = 16 ^ (m * m + 1) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
      have e2 : (25 : ℕ) ^ (m * m + 2) = 625 * 25 ^ (m * m) := by
        rw [show m * m + 2 = (m * m) + 2 by omega, pow_add]
        ring
      rw [e1]
      calc 16 ^ (m * m + 1) = 16 * 16 ^ (m * m) := by rw [pow_succ']
        _ ≤ 16 * 25 ^ (m * m) :=
            Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by norm_num) _)
        _ < 625 * 25 ^ (m * m) := by
            have hpos : (0 : ℕ) < 25 ^ (m * m) := pow_pos (by norm_num) _
            omega
        _ = (25 : ℕ) ^ (m * m + 2) := e2.symm
    omega
  omega

private theorem block_lemma (k : ℕ) (hk : 4 ≤ k) :
    (47 * (k + 1)) ^ 2 + 12 < 46 * 47 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e1 : k + 1 - 1 = k := by omega
    have hpow : (47 : ℕ) ^ k = 47 * 47 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    have hle : (47 * (k + 2)) ^ 2 ≤ 47 * (47 * (k + 1)) ^ 2 := by
      have h1 : k + 2 ≤ 6 * (k + 1) := by omega
      have h2 : (k + 2) ^ 2 ≤ (6 * (k + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      have h3 : (6 * (k + 1)) ^ 2 = 36 * (k + 1) ^ 2 := by ring
      have h4 : (47 * (k + 2)) ^ 2 = 47 ^ 2 * (k + 2) ^ 2 := by ring
      have h5 : 47 * (47 * (k + 1)) ^ 2 = 47 ^ 2 * (47 * (k + 1) ^ 2) := by ring
      rw [h4, h5]
      have h6 : (k + 2) ^ 2 ≤ 47 * (k + 1) ^ 2 := by omega
      exact Nat.mul_le_mul_left _ h6
    have e2 : k + 1 + 1 = k + 2 := by omega
    rw [e2, show (k + 1) - 1 = k from by omega, hpow]
    have ih47 : 47 * ((47 * (k + 1)) ^ 2 + 12) < 47 * (46 * 47 ^ (k - 1)) :=
      Nat.mul_lt_mul_of_pos_left ih (by norm_num)
    omega

private theorem stageA {m n : ℕ} (hn : 2 ≤ n)
    (h : Nat.factorial m + 1 = tribonacci n ^ 2) : m < 188 := by
  by_contra hm188
  have hm : 188 ≤ m := by omega
  have hlow := factorial_factorization_lower m
  have hk0 : 4 ≤ m / 47 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 47)]
    omega
  have hn_le := index_le_of_eq hn h
  rcases valuation_cases (by omega : 1 ≤ n) h with h0 | ⟨r, hfac, hpow, hR⟩
  · omega
  · have hvp : m / 47 - 1 ≤ padicValInt 47 r := by omega
    have h47R : 47 ^ (m / 47 - 1) ≤ r.natAbs :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hvp) hpow
    have hblock := block_lemma (m / 47) hk0
    have hm_lt : m < 47 * (m / 47 + 1) := by
      have hdm := Nat.div_add_mod m 47
      have hmod : m % 47 < 47 := Nat.mod_lt _ (by norm_num)
      omega
    have hmsq : m * m ≤ (47 * (m / 47 + 1)) ^ 2 := by
      have hle : m ≤ 47 * (m / 47 + 1) := le_of_lt hm_lt
      calc m * m ≤ (47 * (m / 47 + 1)) * (47 * (m / 47 + 1)) :=
            Nat.mul_le_mul hle hle
        _ = (47 * (m / 47 + 1)) ^ 2 := by rw [pow_two]
    have h46R : 46 * 47 ^ (m / 47 - 1) ≤ 46 * r.natAbs := Nat.mul_le_mul_left 46 h47R
    have h46 : 46 * r.natAbs ≤ m * m + 12 := by omega
    omega

private theorem pow188 (m : ℕ) (hm : 1 ≤ m) : 2 * 188 ^ m < 625 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 2 * 188 ^ (k + 1) = 188 * (2 * 188 ^ k) := by rw [pow_succ]; ring
      _ < 188 * 625 ^ k := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ < 625 * 625 ^ k := by
          apply Nat.mul_lt_mul_of_pos_right (by norm_num)
          exact pow_pos (by norm_num) k
      _ = 625 ^ (k + 1) := by rw [pow_succ]; ring

private theorem stageB {m n : ℕ} (hn : 2 ≤ n) (hm188 : m < 188)
    (h : Nat.factorial m + 1 = tribonacci n ^ 2) : m < 94 := by
  by_contra hm94
  have hm : 94 ≤ m := by omega
  obtain ⟨t, s, hs, hns⟩ := decomp n hn
  have h5 : 5 ^ t ≤ tribonacci (4 * t + 2) := trib_ge_five_pow t
  have hmono : tribonacci (4 * t + 2) ≤ tribonacci n := trib_mono (by omega)
  have h25m : (25 : ℕ) ^ t ≤ 2 * m ^ m := by
    have hsq : (5 ^ t) ^ 2 ≤ tribonacci n ^ 2 :=
      Nat.pow_le_pow_left (le_trans h5 hmono) 2
    have h25t : (25 : ℕ) ^ t = (5 ^ t) ^ 2 := by
      rw [show (25 : ℕ) = 5 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [h25t]
    have hf : Nat.factorial m ≤ m ^ m := Nat.factorial_le_pow m
    have hpos : (0 : ℕ) < m ^ m := pow_pos (by omega) m
    omega
  have ht : t < 2 * m := by
    by_contra hcon
    have hge : 2 * m ≤ t := by omega
    have h1 : (25 : ℕ) ^ (2 * m) ≤ (25 : ℕ) ^ t := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : (25 : ℕ) ^ (2 * m) = 625 ^ m := by
      rw [show (625 : ℕ) = 25 ^ 2 by norm_num, ← pow_mul]
    have h3 : m ^ m ≤ 188 ^ m := Nat.pow_le_pow_left (by omega) m
    have h4 := pow188 m (by omega)
    omega
  have hlow := factorial_factorization_lower m
  have hk0 : 2 ≤ m / 47 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 47)]
    omega
  rcases valuation_cases (by omega : 1 ≤ n) h with h0 | ⟨r, hfac, hpow, hR⟩
  · omega
  · have hvp : 1 ≤ padicValInt 47 r := by omega
    have h47R : (47 : ℕ) ≤ r.natAbs := by
      have h47 : (47 : ℕ) ^ 1 ≤ 47 ^ padicValInt 47 r :=
        Nat.pow_le_pow_right (by norm_num) hvp
      rw [pow_one] at h47
      exact le_trans h47 hpow
    have h46 : 46 * r.natAbs ≤ m * m + 12 := by
      have hn_le := index_le_of_eq hn h
      omega
    omega

private def tribTriple : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 1)
  | k + 1 => ((tribTriple k).2.1, (tribTriple k).2.2,
      (tribTriple k).1 + (tribTriple k).2.1 + (tribTriple k).2.2)

private theorem tribTriple_eq (k : ℕ) :
    tribTriple k = (tribonacci k, tribonacci (k + 1), tribonacci (k + 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : tribTriple (k + 1) = ((tribTriple k).2.1, (tribTriple k).2.2,
        (tribTriple k).1 + (tribTriple k).2.1 + (tribTriple k).2.2) := rfl
    rw [hstep, ih]
    have h3 : tribonacci (k + 3) = tribonacci (k + 2) + tribonacci (k + 1) + tribonacci k :=
      trib_rec k
    have e2 : k + 1 + 2 = k + 3 := by omega
    change (tribonacci (k + 1), tribonacci (k + 2),
      tribonacci k + tribonacci (k + 1) + tribonacci (k + 2)) =
      (tribonacci (k + 1), tribonacci (k + 1 + 1), tribonacci (k + 3))
    rw [e2, h3]
    simp only [Prod.mk.injEq]
    refine ⟨trivial, trivial, ?_⟩
    omega

private theorem tribonacci_eq_fst (k : ℕ) : tribonacci k = (tribTriple k).1 := by
  rw [tribTriple_eq]

private def brocardTable : List (ℕ × ℕ × ℕ × ℕ × ℕ × Bool) :=
  [
  (0, 0, 1, 0, 0, false),
  (1, 0, 1, 0, 0, false),
  (2, 0, 1, 0, 0, false),
  (3, 0, 2, 0, 0, false),
  (4, 5,
    5,
    4,
    7,
    true),
  (5, 6,
    11,
    7,
    13,
    true),
  (6, 8,
    26,
    24,
    44,
    true),
  (7, 9,
    71,
    44,
    81,
    true),
  (8, 11,
    200,
    149,
    274,
    true),
  (9, 13,
    602,
    504,
    927,
    true),
  (10, 15,
    1904,
    1705,
    3136,
    true),
  (11, 17,
    6317,
    5768,
    10609,
    true),
  (12, 19,
    21886,
    19513,
    35890,
    true),
  (13, 21,
    78911,
    66012,
    121415,
    true),
  (14, 23,
    295259,
    223317,
    410744,
    true),
  (15, 25,
    1143535,
    755476,
    1389537,
    true),
  (16, 27,
    4574143,
    2555757,
    4700770,
    true),
  (17, 30,
    18859677,
    15902591,
    29249425,
    true),
  (18, 32,
    80014834,
    53798080,
    98950096,
    true),
  (19, 35,
    348776576,
    334745777,
    615693474,
    true),
  (20, 37,
    1559776268,
    1132436852,
    2082876103,
    true),
  (21, 40,
    7147792818,
    7046319384,
    12960201916,
    true),
  (22, 42,
    33526120082,
    23837527729,
    43844049029,
    true),
  (23, 45,
    160785623545,
    148323355432,
    272809183135,
    true),
  (24, 47,
    787685471322,
    501774317241,
    922906855808,
    true),
  (25, 50,
    3938427356614,
    3122171529233,
    5742568741225,
    true),
  (26, 53,
    20082117944245,
    19426970897100,
    35731770264967,
    true),
  (27, 55,
    104349745809073,
    65720971788709,
    120879712950776,
    true),
  (28, 58,
    552166953567228,
    408933139743937,
    752145307699165,
    true),
  (29, 61,
    2973510046012910,
    2544489349890656,
    4680045560037375,
    true),
  (30, 64,
    16286585271694955,
    15832480722303616,
    29120472094716576,
    true),
  (31, 66,
    90679869067935485,
    53560898629395777,
    98513851446415969,
    true),
  (32, 69,
    512962802680363491,
    333269972246340068,
    612979045863284359,
    true),
  (33, 72,
    2946746955341073478,
    2073693258389777176,
    3814116544533214284,
    true),
  (34, 75,
    17182339742875652406,
    12903063846126135669,
    23732434433862494162,
    true),
  (35, 78,
    101652092779175702171,
    80286250603180403871,
    147669437360234672073,
    true),
  (36, 81,
    609912556675054213027,
    499562128250021925928,
    918838005896863447985,
    true),
  (37, 84,
    3709953246501409085690,
    3108406708580377597810,
    5717251288910733269692,
    true),
  (38, 87,
    22869687743093501007951,
    19341322569415713958901,
    35574238430251050319992,
    true),
  (39, 90,
    142821154179615294686593,
    120346786571258131649185,
    221352250573100549339469,
    true),
  (40, 93,
    903280290523322408635610,
    748829299860308729347600,
    1377311813149359327046015,
    true),
  (41, 96,
    5783815921445270815783609,
    4659412488735286161146176,
    8569995677610263592944752,
    true),
  (42, 99,
    37483411234209726053065805,
    28992087708416717612934417,
    53324762928098149064722658,
    true),
  (43, 102,
    245795164849461258960674062,
    180396380815100901214157639,
    331800673921785084815380861,
    true),
  (44, 105,
    1630420674178430788228519563,
    1122473639652358006595577564,
    2064550898489615111976997489,
    true),
  (45, 108,
    10937194378152021970306618007,
    6984325661199418257711189170,
    12846177682746478508826800776,
    true),
  (46, 111,
    74179661362209580727623742159,
    43458307810949238672214594009,
    79932289960699059086717998848,
    true),
  (47, 115,
    508550136674023695658451670185,
    497359692209650636174868985545,
    914787094458602213263019972242,
    true),
  (48, 118,
    3523338699662022653505900576721,
    3094702573346805636299319705351,
    5692045454483960636423770425157,
    true),
  (49, 121,
    24663370897634158574541304037050,
    19256051842340085332307611008580,
    35417401111333365028315902311809,
    true),
  (50, 124,
    174396368086360611696209329639024,
    119816209721856219780831547518850,
    220376367601372354229355484029120,
    true),
  (51, 127,
    1245439180886558699493562057691804,
    745527911414639917440582097294401,
    1371239613107423615100332647069952,
    true),
  (52, 131,
    8980989654316715588967781706572076,
    8532212854856436899583867011655873,
    15693186096605450184067401376241794,
    true),
  (53, 134,
    65382591597917144387816492317568177,
    53089668286059312575814761330270471,
    97647123717262188252045655648885069,
    true),
  (54, 137,
    480461962427038942460267525096444474,
    330337853341240427147884326900683884,
    607586038396421541719953892471097297,
    true),
  (55, 140,
    3563201278858419461033351267854721464,
    2055448844813242864055700348665090706,
    3780559836285245300963516370429497528,
    true),
  (56, 144,
    26664556771205919519070097139612996000,
    23523635785731871586396890786299881280,
    43266711735178497871830265202170265032,
    true),
  (57, 147,
    201312988912482288333668455069536465757,
    146370237357093296141680607544422778617,
    269216838928454720696964324302545675954,
    true),
  (58, 150,
    1533154046820761769413164705689608744377,
    910754042407278960360743315249889541447,
    1675137847457464624579806022955356304277,
    true),
  (59, 154,
    11776379687564843276211019969710858039009,
    10423147449295157266445650804376936015201,
    19171157051132849908311495585798515726125,
    true),
  (60, 157,
    91219444817107882594696857529818207676198,
    64855559746707232462917489840164316260976,
    119287972044119307659389328875951696506751,
    true),
  (61, 160,
    712446639319201784948673912308403605115342,
    403548318827932305532773980882220890055104,
    742241077909157378602630471924277463849232,
    true),
  (62, 164,
    5609810447812647575362248801595614968784558,
    4618418842194637961829778154675982280136994,
    8494596606480118545056925837427687096424756,
    true),
  (63, 167,
    44526490041372451122965980435912297622389065,
    28737014477860798147454684051986440338219549,
    52855610113526958333079589949296898396302104,
    true),
  (64, 171,
    356211920330979608983727843487298380979112523,
    328881481946062311055818372072912456523182661,
    604907353778597663778557154196528014650063218,
    true),
  (65, 174,
    2871872314724746021942727901945240734448707786,
    2046386919661281504270387580601330390777192863,
    3763892357376500697484956789129748325031203065,
    true),
  (66, 177,
    23331200978034608323876057832648816217523382535,
    12733156638012185932946700793794047351220738840,
    23419926356363090361623014006986764311664284817,
    true),
  (67, 181,
    190974110596668796970008672429388554580114244205,
    145724930061437726707714871257455136571144041612,
    268029933766512363053806728507923508830623798407,
    true),
  (68, 184,
    1574812859496908794403637793960093262759360945119,
    906738771005625135843373985556381882764718070264,
    1667752611949812544979033099855308628958292098916,
    true),
  (69, 188,
    13081378078327271990661335578798848847474255303826,
    10377194575171475679609959127672386638853223066946,
    19086636538393138814240885155489464648748154034976,
    true),
  (70, 191,
    109446661301155695857080695109221322834464193656741,
    64569628900217779395428355122938086836011724772449,
    118762063225264083111246751118203787033170226477952,
    true),
  (71, 195,
    922213960297642814598347871007016379244405330655250,
    738968735175016000434427091521181879737536775570209,
    1359175407124767917757607431924159972441903324662466,
    true),
  (72, 198,
    7825244940376376925358096892704591704511772131306815,
    4598057466637184726298996770212743687645654450636679,
    8457146198099353452163566448904305495553772125703149,
    true),
  (73, 202,
    66858922078602825324590583356376523422703411874063526,
    52622583840983769603765180599790256716084480555530641,
    96788021483868185755366794750676207936615188985358133,
    true),
  (74, 205,
    575142194723999224356836312510183507170717503745407529,
    327431531303514387883296039385934429507264406584861208,
    602240478766045006162826898172078602298444332614191775,
    true),
  (75, 209,
    4980877514193196669713282991946078429827937232372941867,
    3747298360932048053349523838917053627424700024299295592,
    6892356243098051100536220779662028652550955715984399409,
    true),
  (76, 213,
    43422283469044442400520987277954690033900570230313299933,
    42886049947423911003426274513702263549409887367719641212,
    78879743651749770906316328247742498446268819019454883015,
    true),
  (77, 216,
    381028991060110634246276414878912279469899189376847948137,
    266848261352525343347873104699199182579774706470358516856,
    490810472757626775692319934884696101610139525572997392500,
    true),
  (78, 220,
    3365156932181068109459677272856044111292549448241189337343,
    3053951610594786455689160057511890795348074221869433105826,
    5617092748431946135686000180139085489086008918165868819152,
    true),
  (79, 223,
    29910169058002623210200515287548862104836069367192860122492,
    19002488654027121082268837056407497557832090744240499661297,
    34951025697459455708848514055303104320316107266611566216768,
    true),
  (80, 227,
    267524684928818862621490012042605003730753817304274266583374,
    217474457341919963063987921027947952501556716507578159323601,
    399997888986380470419127328000592800682797325748544752430434,
    true),
  (81, 230,
    2407722164359369763593410108383445033576784355738468399250368,
    1353183165654574409039358877099259231398402488138155153000519,
    2488891873967228855014729833170570510295248259768732146677437,
    true),
  (82, 234,
    21802851503903891305843592056331800458090082265244558375673041,
    15486538631485186598289483220121496691804297395253458528204273,
    28484185389003144341564236607072422873313346530738184909731109,
    true),
  (83, 238,
    198633430462262788036763464177703883166690275063913206990548481,
    177236079247607898168454238185874937491868978192104728904742047,
    325987973106212651995344239764677452110424609853471272899752985,
    true),
  (84, 241,
    1820505461284132832359203813645046756110583331925714370170257092,
    1102809413647187642710968816604102996296423813884831097325463224,
    2028382748046767387253483395022331055100978649577557465746184401,
    true),
  (85, 245,
    16784231035053557904028966906346483792025484094796637394973403970,
    12621129955715366662241180707208734422681446491643233346003063660,
    23213877163383965937228878019395137790261914333708909226259942919,
    true),
  (86, 249,
    155650555359345674201535001388480503193835670087005087695666582899,
    144442837890044518040591203723019591848069867115293401386377489540,
    265671798616705070143953529426644045905877819896877893546495036161,
    true),
  (87, 252,
    1451811729660401840498379775717372701145990271033308799231637667601,
    898761256936379118720505658514441438643271030827810907231935328002,
    1653079675982713719400420113305863285438472194540328413077493166464,
    true),
  (88, 256,
    13619201234191322393627253212934023042404388731461906952430812397994,
    10285895715599251294835119279496333059462348558276025598603904254464,
    18918711755215788870269818445686802833486224922011722784130315342464,
    true),
  (89, 260,
    128483287477042947436606854413089420338280480054241478815100633956558,
    117717191140196539779140256559246985010437564951978804438168813715714,
    216515670525177290688010694672807167187388904981945886092207312088964,
    true),
  (90, 263,
    1218899489080933816973227253068021382231629321448981884930371490328689,
    732467266758645556471289590383479963430602896622976796079138610594445,
    1347217342377094573163438924207712941850768228293974787720108407473176,
    true),
  (91, 267,
    11627560052213890684239693812535151882288553865765313903995958273943586,
    8382739979970858414075901746284143280160434456422933750215374431255573,
    15418262617564622254988364568360573618470100684551892712710640455037970,
    true),
  (92, 271,
    111527638075238136262755547542307772029800712447380847367329167783382104,
    95936477656900568232728354848962347557952743460522282647783198155768617,
    176454692696236514210468345129564121497435386236492672582855755856499264,
    true),
  (93, 274,
    1075533591796017115343430456551200439746548977577162936545074776552498754,
    596941949524709878209795528254676183529832848352502518660277194318047857,
    1097947421392519188186862701660390019501712953244482754672771190480327097,
    true),
  ]

set_option maxRecDepth 8192 in
private theorem brocardTable_check : ∀ e ∈ brocardTable,
    (tribTriple e.2.1).1 = e.2.2.2.1 ∧ (tribTriple (e.2.1 + 1)).1 = e.2.2.2.2.1 ∧
      e.2.2.1 * e.2.2.1 ≤ Nat.factorial e.1 + 1 ∧
        Nat.factorial e.1 + 1 < (e.2.2.1 + 1) * (e.2.2.1 + 1) ∧
      (e.2.2.2.2.2 → e.2.2.2.1 < e.2.2.1 ∧ e.2.2.1 < e.2.2.2.2.1) ∧
      (¬ e.2.2.2.2.2 → e.2.2.1 * e.2.2.1 < Nat.factorial e.1 + 1) := by
  decide

private theorem brocardTable_lookup : ∀ m : ℕ, m < 94 →
    ∃ e ∈ brocardTable, e.1 = m := by
  decide

private theorem finite_check {m n : ℕ} (hm : m < 94)
    (h : Nat.factorial m + 1 = tribonacci n ^ 2) : False := by
  obtain ⟨e, he, hem⟩ := brocardTable_lookup m hm
  obtain ⟨htk, htk1, hs1, hs2, hgap, hnsq⟩ := brocardTable_check e he
  subst hem
  have hTs : tribonacci n = e.2.2.1 := by
    apply le_antisymm
    · by_contra hcon
      have hlt : e.2.2.1 < tribonacci n := Nat.lt_of_not_ge hcon
      have hle : (e.2.2.1 + 1) * (e.2.2.1 + 1) ≤ tribonacci n * tribonacci n :=
        Nat.mul_le_mul (by omega) (by omega)
      have hsq2 : tribonacci n ^ 2 = tribonacci n * tribonacci n := pow_two _
      omega
    · by_contra hcon
      have hlt : tribonacci n < e.2.2.1 := Nat.lt_of_not_ge hcon
      have hle : (tribonacci n + 1) * (tribonacci n + 1) ≤ e.2.2.1 * e.2.2.1 :=
        Nat.mul_le_mul (by omega) (by omega)
      have hsq2 : tribonacci n ^ 2 = tribonacci n * tribonacci n := pow_two _
      have hlt2 : tribonacci n * tribonacci n < (tribonacci n + 1) * (tribonacci n + 1) := by
        have hp : (tribonacci n) ^ 2 < (tribonacci n + 1) ^ 2 :=
          Nat.pow_lt_pow_left (show tribonacci n < tribonacci n + 1 by omega)
            (by norm_num : (2 : ℕ) ≠ 0)
        rwa [pow_two, pow_two] at hp
      omega
  by_cases hg : e.2.2.2.2.2
  · obtain ⟨hlt1, hlt2⟩ := hgap hg
    have htk' : tribonacci e.2.1 = e.2.2.2.1 := by rw [tribonacci_eq_fst, htk]
    have htk1' : tribonacci (e.2.1 + 1) = e.2.2.2.2.1 := by rw [tribonacci_eq_fst, htk1]
    by_cases hnle : n ≤ e.2.1
    · have hle := trib_mono hnle
      omega
    · have hle := trib_mono (show e.2.1 + 1 ≤ n by omega)
      omega
  · have hlt := hnsq hg
    rw [hTs, pow_two] at h
    omega

end brocardRamanujan_not_tribonacci

/--
**The Tribonacci number of index $-10$.** Let $(T_n)_{n \in \mathbb{Z}}$ be the two-sided
Tribonacci sequence, determined by $T_0 = 0$, $T_1 = T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$ for all integers $n$. Then $T_{-10} = 5$.

Since $4! + 1 = 5^2$, the equation $m! + 1 = T_n^2$ has a solution once negative indices $n$ are
allowed.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci
Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1 normalization note.
-/
public theorem tribonacciInt_neg_ten : tribonacciInt (-10) = 5 := by
  rfl

/--
**The Brocard–Ramanujan equation has no Tribonacci solutions.** Let $(T_n)_{n \ge 0}$ be the
Tribonacci sequence, given by $T_0 = T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$
for $n \ge 0$. For all natural numbers $m$ and $n$, $m! + 1 \ne T_n^2$.

Only nonnegative indices are allowed: the extension of the Tribonacci sequence to negative indices
by the same recurrence takes the value $5$, and $4! + 1 = 5^2$.

Source: Paul Thomas Young, *On the Brocard-Ramanujan Equation with Tribonacci and Tetranacci
Numbers*, INTEGERS 24 (2024), Article A92, Theorem 1.
-/
public theorem brocardRamanujan_not_tribonacci :
    ∀ m n : ℕ, Nat.factorial m + 1 ≠ tribonacci n ^ 2 := by
  intro m n h
  by_cases hn : n < 2
  · interval_cases n
    · rw [show tribonacci 0 = 0 from rfl] at h
      have hpos := Nat.factorial_pos m
      omega
    · rw [show tribonacci 1 = 0 from rfl] at h
      have hpos := Nat.factorial_pos m
      omega
  · have hn2 : 2 ≤ n := by omega
    by_cases hm94 : m < 94
    · exact brocardRamanujan_not_tribonacci.finite_check hm94 h
    · have hm188 := brocardRamanujan_not_tribonacci.stageA hn2 h
      have hm94' := brocardRamanujan_not_tribonacci.stageB hn2 hm188 h
      omega

end MetaMathlibExt
