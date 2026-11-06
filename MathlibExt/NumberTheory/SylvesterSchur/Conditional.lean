/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import MathlibExt.NumberTheory.SylvesterSchur.Bridge
public import MathlibExt.NumberTheory.SylvesterSchur.LargePrimeCriteria

/-!
# Conditional Sylvester-Schur consequences

This file connects the small binomial coefficient estimates to the consecutive-integer
form. The remaining hard work is to prove estimates such as
`n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n` in the required range.
-/

@[expose] public section

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-- **Sylvester–Schur theorem for two consecutive integers.** For every natural number $k > 2$,
one of the two integers $k$, $k + 1$ is divisible by a prime $p > 2$. -/
theorem consecutive_two {k : ℕ} (hk : 2 < k) :
    ∃ i : ℕ, i < 2 ∧ ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ k + i := by
  by_cases hk_even : 2 ∣ k
  · have hk1_mf_prime : (k + 1).minFac.Prime :=
      Nat.minFac_prime (by omega : k + 1 ≠ 1)
    have hk1_mf_odd : 2 < (k + 1).minFac := by
      by_contra h
      push Not at h
      have htwo_dvd_k1 : 2 ∣ k + 1 :=
        (le_antisymm h hk1_mf_prime.two_le) ▸ (k + 1).minFac_dvd
      omega
    exact ⟨1, by omega, (k + 1).minFac, hk1_mf_prime, hk1_mf_odd,
      by simpa using (k + 1).minFac_dvd⟩
  · have hk_mf_prime : k.minFac.Prime := Nat.minFac_prime (by omega : k ≠ 1)
    have hk_mf_odd : 2 < k.minFac := by
      by_contra h
      push Not at h
      exact hk_even ((le_antisymm h hk_mf_prime.two_le) ▸ k.minFac_dvd)
    exact ⟨0, by omega, k.minFac, hk_mf_prime, hk_mf_odd, by simpa using k.minFac_dvd⟩

/- A number greater than one and coprime to `6` has a prime divisor greater than `3`. -/
private lemma exists_prime_gt_three_dvd_of_not_two_dvd_of_not_three_dvd {m : ℕ}
    (hm : 1 < m) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ m := by
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, ?_, hdvd⟩
  by_contra hle
  push Not at hle
  have hp_two : 2 ≤ p := hp.two_le
  interval_cases p
  · exact h2 hdvd
  · exact h3 hdvd

/- A number greater than one and coprime to `30` has a prime divisor greater than `5`. -/
private lemma exists_prime_gt_five_dvd_of_not_two_dvd_of_not_three_dvd_of_not_five_dvd
    {m : ℕ} (hm : 1 < m) (h2 : ¬ 2 ∣ m) (h3 : ¬ 3 ∣ m) (h5 : ¬ 5 ∣ m) :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ m := by
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, ?_, hdvd⟩
  by_contra hle
  push Not at hle
  have hp_two : 2 ≤ p := hp.two_le
  interval_cases p
  · exact h2 hdvd
  · exact h3 hdvd
  · norm_num at hp
  · exact h5 hdvd

private lemma four_lt_of_prime_of_three_lt {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 4 < p := by
  have hp_ne_four : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

private lemma six_lt_of_prime_of_five_lt {p : ℕ} (hp : p.Prime) (h5 : 5 < p) : 6 < p := by
  have hp_ne_six : p ≠ 6 := by
    rintro rfl
    norm_num at hp
  omega

private lemma half_witness_three {k i : ℕ} (hi : i < 3) (hm : 1 < (k + i) / 2)
    (heven : 2 ∣ k + i) (hcop : ¬ 2 ∣ (k + i) / 2 ∧ ¬ 3 ∣ (k + i) / 2) :
    ∃ i m, i < 3 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m := by
  exact ⟨i, (k + i) / 2, hi, hm, Nat.div_dvd_of_dvd heven, hcop.1, hcop.2⟩

private lemma half_witness_five {k i : ℕ} (hi : i < 5) (hm : 1 < (k + i) / 2)
    (heven : 2 ∣ k + i)
    (hcop : ¬ 2 ∣ (k + i) / 2 ∧ ¬ 3 ∣ (k + i) / 2 ∧ ¬ 5 ∣ (k + i) / 2) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  exact ⟨i, (k + i) / 2, hi, hm, Nat.div_dvd_of_dvd heven, hcop.1, hcop.2.1,
    hcop.2.2⟩

/- A finite witness certificate for the length-three consecutive theorem. -/
private lemma consecutive_three_witness {k : ℕ} (hk : 3 < k) :
    ∃ i m, i < 3 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m := by
  have hlt : k % 12 < 12 := Nat.mod_lt k (by norm_num)
  interval_cases hmod : k % 12
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact half_witness_three (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact half_witness_three (i := 2) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega⟩

/-- **Sylvester–Schur theorem for three consecutive integers.** For every natural number
$k > 3$, one of the three integers $k$, $k + 1$, $k + 2$ is divisible by a prime $p > 3$. -/
theorem consecutive_three {k : ℕ} (hk : 3 < k) :
    ∃ i : ℕ, i < 3 ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ k + i := by
  obtain ⟨i, m, hi, hm, hmdvd, h2, h3⟩ := consecutive_three_witness hk
  obtain ⟨p, hp, hp_gt, hp_dvd⟩ :=
    exists_prime_gt_three_dvd_of_not_two_dvd_of_not_three_dvd hm h2 h3
  exact ⟨i, hi, p, hp, hp_gt, hp_dvd.trans hmdvd⟩

/-- **Four consecutive integers above four have a prime factor above four.** For every natural
number $k > 4$, some prime $p > 4$ divides one of $k$, $k+1$, $k+2$, $k+3$. -/
theorem consecutive_four {k : ℕ} (hk : 4 < k) :
    ∃ i : ℕ, i < 4 ∧ ∃ p : ℕ, p.Prime ∧ 4 < p ∧ p ∣ k + i := by
  obtain ⟨i, hi, p, hp, hp_gt_three, hp_dvd⟩ := consecutive_three (k := k) (by omega)
  exact ⟨i, by omega, p, hp, four_lt_of_prime_of_three_lt hp hp_gt_three, hp_dvd⟩

/- The finite residue certificate for the length-five consecutive theorem. -/
private lemma consecutive_five_witness_mod_lt_fifteen {k : ℕ} (hk : 5 < k)
    (hmod_lt : k % 60 < 15) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  interval_cases hmod : k % 60
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨4, k + 4, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨3, k + 3, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨3, k + 3, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)

private lemma consecutive_five_witness_mod_fifteen_to_twenty_nine {k : ℕ} (hk : 5 < k)
    (hmod_ge : 15 ≤ k % 60) (hmod_lt : k % 60 < 30) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  interval_cases hmod : k % 60
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 2) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 1) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 2) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 1) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩

private lemma consecutive_five_witness_mod_thirty_to_forty_four {k : ℕ} (hk : 5 < k)
    (hmod_ge : 30 ≤ k % 60) (hmod_lt : k % 60 < 45) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  interval_cases hmod : k % 60
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 2) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 1) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 2) (by norm_num) (by omega) (by omega) (by omega)

private lemma consecutive_five_witness_mod_forty_five_to_fifty_nine {k : ℕ} (hk : 5 < k)
    (hmod_ge : 45 ≤ k % 60) (hmod_lt : k % 60 < 60) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  interval_cases hmod : k % 60
  · exact half_witness_five (i := 1) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨3, k + 3, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨2, k + 2, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨1, k + 1, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩
  · exact half_witness_five (i := 4) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 3) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 2) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 1) (by norm_num) (by omega) (by omega) (by omega)
  · exact half_witness_five (i := 0) (by norm_num) (by omega) (by omega) (by omega)
  · exact ⟨0, k, by norm_num, by omega, by simp, by omega, by omega, by omega⟩

/- A finite witness certificate for the length-five consecutive theorem. It chooses
a term, or half of an even term, that is coprime to `2`, `3`, and `5`. -/
private lemma consecutive_five_witness {k : ℕ} (hk : 5 < k) :
    ∃ i m, i < 5 ∧ 1 < m ∧ m ∣ k + i ∧ ¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m := by
  by_cases h15 : k % 60 < 15
  · exact consecutive_five_witness_mod_lt_fifteen hk h15
  by_cases h30 : k % 60 < 30
  · exact consecutive_five_witness_mod_fifteen_to_twenty_nine hk (by omega) h30
  by_cases h45 : k % 60 < 45
  · exact consecutive_five_witness_mod_thirty_to_forty_four hk (by omega) h45
  exact consecutive_five_witness_mod_forty_five_to_fifty_nine hk (by omega)
    (Nat.mod_lt k (by norm_num))

/- The finite residue certificate for the length-five consecutive theorem. -/
private lemma consecutive_five_finite_certificate {k : ℕ} (hk : 5 < k) :
    ∃ i : ℕ, i < 5 ∧ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ k + i := by
  obtain ⟨i, m, hi, hm, hmdvd, h2, h3, h5⟩ := consecutive_five_witness hk
  obtain ⟨p, hp, hp_gt, hp_dvd⟩ :=
    exists_prime_gt_five_dvd_of_not_two_dvd_of_not_three_dvd_of_not_five_dvd
      hm h2 h3 h5
  exact ⟨i, hi, p, hp, hp_gt, hp_dvd.trans hmdvd⟩

/-- **Five consecutive integers above five have a prime factor above five.** For every natural
number $k > 5$, some prime $p > 5$ divides one of $k$, $k+1$, $k+2$, $k+3$, $k+4$. -/
theorem consecutive_five {k : ℕ} (hk : 5 < k) :
    ∃ i : ℕ, i < 5 ∧ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ k + i :=
  consecutive_five_finite_certificate hk

/-- **Six consecutive integers above six have a prime factor above six.** For every natural
number $k > 6$, some prime $p > 6$ divides one of $k$, $k+1$, $k+2$, $k+3$, $k+4$, $k+5$. -/
theorem consecutive_six {k : ℕ} (hk : 6 < k) :
    ∃ i : ℕ, i < 6 ∧ ∃ p : ℕ, p.Prime ∧ 6 < p ∧ p ∣ k + i := by
  obtain ⟨i, hi, p, hp, hp_gt_five, hp_dvd⟩ := consecutive_five (k := k) (by omega)
  exact ⟨i, by omega, p, hp, six_lt_of_prime_of_five_lt hp hp_gt_five, hp_dvd⟩

/-- **Prime-counting criterion for a large prime in a consecutive block.** Let $1 \le n < k$ be
natural numbers and let $\pi(n)$ be the number of primes at most $n$. If
$n! \cdot (k+n-1)^{\pi(n)} < k^n$, then some prime $p > n$ divides one of the integers
$k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound : n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_top_pow_primeCounting_lt_lower_pow
    (by omega) (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/-- **Half-exponent criterion for a large prime in a consecutive block.** Let $1 \le n < k$ be
natural numbers. If $n! \cdot (k+n-1)^{\lfloor n/2 \rfloor + 1} < k^n$, then some prime $p > n$
divides one of the integers $k, k+1, \dots, k+n-1$.

The exponent comes from the bound $\pi(n) \le \lfloor n/2 \rfloor + 1$ on the prime-counting
function $\pi$. -/
theorem consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound : n ! * (k + n - 1) ^ (n / 2 + 1) < k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_top_pow_half_add_one_lt_lower_pow
    (by omega) (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/- Power-only consecutive form of the `3n/8` criterion, using `n! ≤ n ^ n`. -/
private lemma consecutive_of_self_pow_mul_top_pow_three_mul_div_eight_lt_start_pow
    {n k : ℕ} (hn : 38 ≤ n) (hk : n < k)
    (hbound : n ^ n * (k + n - 1) ^ (3 * n / 8) < k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_self_pow_mul_top_pow_three_mul_div_eight_lt_lower_pow
    (by omega) hn (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/- Pure-power large-start form of the `3n/8` criterion. -/
private lemma consecutive_of_three_eighth_self_pow_large_start {n k : ℕ} (hn : 38 ≤ n)
    (hk : n < k) (hlarge : n ^ n * 2 ^ (3 * n / 8) < k ^ (n - 3 * n / 8)) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_self_pow_mul_top_pow_three_mul_div_eight_lt_start_pow hn hk
  calc
    n ^ n * (k + n - 1) ^ (3 * n / 8) ≤ n ^ n * (2 * k) ^ (3 * n / 8) := by
      exact Nat.mul_le_mul_left (n ^ n)
        (Nat.pow_le_pow_left (by omega : k + n - 1 ≤ 2 * k) (3 * n / 8))
    _ = n ^ n * (2 ^ (3 * n / 8) * k ^ (3 * n / 8)) := by
      rw [Nat.mul_pow]
    _ = (n ^ n * 2 ^ (3 * n / 8)) * k ^ (3 * n / 8) := by ring
    _ < k ^ (n - 3 * n / 8) * k ^ (3 * n / 8) := by
      exact Nat.mul_lt_mul_of_pos_right hlarge (pow_pos (by omega : 0 < k) (3 * n / 8))
    _ = k ^ n := by
      rw [← pow_add]
      congr 1
      omega

/-- **Quadratic starts give a large prime in a consecutive block.** Let $n \ge 38$ and $k > n^2$
be natural numbers. Then some prime $p > n$ divides one of the integers
$k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_quadratic_start {n k : ℕ} (hn : 38 ≤ n)
    (hkquad : n ^ 2 < k) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_three_eighth_self_pow_large_start hn (by nlinarith [hn, hkquad])
  let e := 3 * n / 8
  have htwo : 2 ^ e ≤ n ^ (n - 2 * e) := by
    have h_exp : e ≤ 4 * (n - 2 * e) := by
      dsimp [e]
      omega
    have h16 : 16 ≤ n := by omega
    calc
      2 ^ e ≤ 2 ^ (4 * (n - 2 * e)) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) h_exp
      _ = 16 ^ (n - 2 * e) := by
        rw [show 4 * (n - 2 * e) = (n - 2 * e) * 4 by ring, Nat.pow_mul']
      _ ≤ n ^ (n - 2 * e) := Nat.pow_le_pow_left h16 (n - 2 * e)
  have hleft : n ^ n * 2 ^ e ≤ n ^ (2 * (n - e)) := by
    calc
      n ^ n * 2 ^ e ≤ n ^ n * n ^ (n - 2 * e) :=
        Nat.mul_le_mul_left (n ^ n) htwo
      _ = n ^ (n + (n - 2 * e)) := by rw [← pow_add]
      _ = n ^ (2 * (n - e)) := by
        congr 1
        omega
  have hmid : n ^ (2 * (n - e)) < k ^ (n - e) := by
    rw [mul_comm 2 (n - e), Nat.pow_mul']
    exact Nat.pow_lt_pow_left hkquad (by omega : n - e ≠ 0)
  exact hleft.trans_lt hmid

/- Conditional consecutive form using only the elementary exponent `n - 1`. -/
private lemma consecutive_of_factorial_mul_top_pow_sub_one_lt_start_pow {n k : ℕ}
    (hn : 2 ≤ n) (hk : n < k)
    (hbound : n ! * (k + n - 1) ^ (n - 1) < k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sub_one_lt_lower_pow
    (by omega) hn (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/-- **Square-root and primorial criterion for a large prime in a consecutive block.** Let
$1 \le n < k$ be natural numbers, write $N = k + n - 1$, and let $P(n)$ denote the product of all
primes at most $n$. If $n! \cdot N^{\lfloor \sqrt{N} \rfloor + 1} \cdot P(n) < k^n$, then some prime
$p > n$ divides one of the integers $k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound :
      n ! * ((k + n - 1) ^ (Nat.sqrt (k + n - 1) + 1) * primorial n) < k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_lower_pow
    (by omega) (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/-- **Erdős layer criterion for a large prime in a consecutive block.** Let $1 \le n < k$ be
natural numbers, write $N = k + n - 1$ and $L = \lfloor \log_2 N \rfloor$, and for a natural number
$m$ let $P(m)$ denote the product of all primes at most $m$. If
$n! \cdot P(n) \cdot \prod_{i=2}^{L} P(\lfloor N^{1/i} \rfloor) < k^n$, then some prime $p > n$
divides one of the integers $k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial n else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_layers_lt_lower_pow
    (by omega) (by omega)
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/-- **Erdős layer criterion with a one-third first layer for a large prime in a consecutive block.**
Let $n < k$ be natural numbers, write $N = k + n - 1$ and $L = \lfloor \log_2 N \rfloor$, assume
$N \ge 6$, and for a natural number $m$ let $P(m)$ denote the product of all primes at most $m$.
If $n! \cdot P(\lfloor N/3 \rfloor) \cdot \prod_{i=2}^{L} P(\lfloor N^{1/i} \rfloor) < k^n$, then
some prime $p > n$ divides one of the integers $k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow {n k : ℕ}
    (hk : n < k) (hN6 : 6 ≤ k + n - 1)
    (hbound :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial ((k + n - 1) / 3)
            else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_exists_prime_dvd_choose
  apply exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_div_three_layers_lt_lower_pow
    (by omega) (by omega) (by omega) hN6
  simpa [show k + n - 1 + 1 - n = k by omega] using hbound

/- A simple sufficient estimate for the preceding conditional theorem: if the starting point is
larger than `n ! * 2 ^ (n - 1)`, then the crude factorization bound already forces a prime
divisor greater than `n`. -/
private lemma factorial_mul_top_pow_sub_one_lt_start_pow_of_large_start {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k) (hlarge : n ! * 2 ^ (n - 1) < k) :
    n ! * (k + n - 1) ^ (n - 1) < k ^ n := by
  have hpow : (k + n - 1) ^ (n - 1) ≤ (2 * k) ^ (n - 1) :=
    Nat.pow_le_pow_left (by omega : k + n - 1 ≤ 2 * k) _
  have hmul : n ! * (k + n - 1) ^ (n - 1) ≤ n ! * (2 * k) ^ (n - 1) :=
    Nat.mul_le_mul_left _ hpow
  have hstrict : n ! * (2 * k) ^ (n - 1) < k ^ n := by
    calc
      n ! * (2 * k) ^ (n - 1)
          = (n ! * 2 ^ (n - 1)) * k ^ (n - 1) := by
            rw [Nat.mul_pow]
            ac_rfl
      _ < k * k ^ (n - 1) :=
          Nat.mul_lt_mul_of_pos_right hlarge (by exact pow_pos (by omega : 0 < k) (n - 1))
      _ = k ^ (n - 1) * k := by rw [Nat.mul_comm]
      _ = k ^ (n - 1 + 1) := by rw [pow_succ]
      _ = k ^ n := by rw [Nat.sub_add_cancel hn]
  exact hmul.trans_lt hstrict

/-- **Large starts give a large prime in a consecutive block.** Let $n \ge 2$ and $k > n$ be
natural numbers with $n! \cdot 2^{n-1} < k$. Then some prime $p > n$ divides one of the integers
$k, k+1, \dots, k+n-1$. -/
theorem consecutive_of_large_start {n k : ℕ} (hn : 2 ≤ n) (hk : n < k)
    (hlarge : n ! * 2 ^ (n - 1) < k) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  apply consecutive_of_factorial_mul_top_pow_sub_one_lt_start_pow hn hk
  exact factorial_mul_top_pow_sub_one_lt_start_pow_of_large_start (by omega) hk hlarge

end Nat.SylvesterSchur
