/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Thabit ibn Qurra's amicable-number theorem

This file proves Thabit ibn Qurra's construction of a pair of amicable numbers.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

private theorem thabit_two_pow_sigma (n : ℕ) :
    ∑ d ∈ Nat.divisors (2 ^ n), d = 2 ^ (n + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  simpa using Nat.geomSum_eq (m := 2) (by norm_num) (n + 1)

private theorem thabit_parameter_successors (n p q r : ℕ) (hn : 2 ≤ n)
    (hp : p = 3 * 2 ^ n - 1) (hq : q = 3 * 2 ^ (n - 1) - 1)
    (hr : r = 9 * 2 ^ (2 * n - 1) - 1) :
    p + 1 = 6 * 2 ^ (n - 1) ∧
      q + 1 = 3 * 2 ^ (n - 1) ∧
      r + 1 = 18 * 2 ^ (n - 1) * 2 ^ (n - 1) := by
  have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = 1 + (n - 1) by omega, pow_add]
    norm_num
  have hpow_two_n : 2 ^ (2 * n - 1) = 2 ^ n * 2 ^ (n - 1) := by
    rw [show 2 * n - 1 = n + (n - 1) by omega, pow_add]
  constructor
  · rw [hp, hpow_n]
    have := Nat.two_pow_pos (n - 1)
    omega
  constructor
  · rw [hq]
    have := Nat.two_pow_pos (n - 1)
    omega
  · rw [hr, hpow_two_n, hpow_n]
    ring_nf
    have := Nat.two_pow_pos ((n - 1) * 2)
    omega

private theorem thabit_parameter_product (n p q r : ℕ) (hn : 2 ≤ n)
    (hp : p = 3 * 2 ^ n - 1) (hq : q = 3 * 2 ^ (n - 1) - 1)
    (hr : r = 9 * 2 ^ (2 * n - 1) - 1) :
    p * q < r ∧
      p * q + r = 9 * 2 ^ (n - 1) * (2 ^ (n + 1) - 1) := by
  obtain ⟨hp1, hq1, hr1⟩ := thabit_parameter_successors n p q r hn hp hq hr
  have ha : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ n - 1 by omega)
    norm_num at h
    exact h
  constructor
  · nlinarith
  · have hpow_next : 2 ^ (n + 1) = 4 * 2 ^ (n - 1) := by
      rw [show n + 1 = 2 + (n - 1) by omega, pow_add]
      norm_num
    rw [hpow_next]
    have hsum : p * q + r + 9 * 2 ^ (n - 1) =
        36 * 2 ^ (n - 1) * 2 ^ (n - 1) := by
      nlinarith
    have hsub : 4 * 2 ^ (n - 1) - 1 + 1 = 4 * 2 ^ (n - 1) := by omega
    apply Nat.add_right_cancel (m := 9 * 2 ^ (n - 1))
    calc
      p * q + r + 9 * 2 ^ (n - 1) =
          36 * 2 ^ (n - 1) * 2 ^ (n - 1) := hsum
      _ = 9 * 2 ^ (n - 1) * (4 * 2 ^ (n - 1)) := by ring
      _ = 9 * 2 ^ (n - 1) * (4 * 2 ^ (n - 1) - 1 + 1) := by rw [hsub]
      _ = 9 * 2 ^ (n - 1) * (4 * 2 ^ (n - 1) - 1) +
          9 * 2 ^ (n - 1) := by ring

private theorem thabit_coprime_data (n p q r : ℕ) (hn : 2 ≤ n)
    (hp : p = 3 * 2 ^ n - 1) (hq : q = 3 * 2 ^ (n - 1) - 1)
    (hr : r = 9 * 2 ^ (2 * n - 1) - 1)
    (pp : Nat.Prime p) (pq : Nat.Prime q) (pr : Nat.Prime r) :
    (2 ^ n).Coprime p ∧ (2 ^ n).Coprime q ∧
      (2 ^ n).Coprime r ∧ p.Coprime q := by
  obtain ⟨hp1, hq1, hr1⟩ := thabit_parameter_successors n p q r hn hp hq hr
  have ha : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ n - 1 by omega)
    norm_num at h
    exact h
  have hp_ne_two : p ≠ 2 := by nlinarith
  have hq_ne_two : q ≠ 2 := by nlinarith
  have hr_ne_two : r ≠ 2 := by nlinarith
  have h2p : (2 ^ n).Coprime p :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (pp.odd_of_ne_two hp_ne_two))
  have h2q : (2 ^ n).Coprime q :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (pq.odd_of_ne_two hq_ne_two))
  have h2r : (2 ^ n).Coprime r :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (pr.odd_of_ne_two hr_ne_two))
  have hqp : q < p := by nlinarith
  have hpq : p.Coprime q := (pp.coprime_iff_not_dvd).mpr fun hdvd => by
    have := Nat.le_of_dvd pq.pos hdvd
    omega
  exact ⟨h2p, h2q, h2r, hpq⟩

private theorem thabit_sigma_pqr (n p q : ℕ)
    (pp : Nat.Prime p) (pq : Nat.Prime q)
    (h2p : (2 ^ n).Coprime p) (h2q : (2 ^ n).Coprime q)
    (hpq : p.Coprime q) :
    ∑ d ∈ Nat.divisors (2 ^ n * p * q), d =
      (2 ^ (n + 1) - 1) * (p + 1) * (q + 1) := by
  rw [(h2q.mul_left hpq).sum_divisors_mul, h2p.sum_divisors_mul,
    thabit_two_pow_sigma, pp.sum_divisors, pq.sum_divisors]

private theorem thabit_sigma_r (n r : ℕ) (pr : Nat.Prime r)
    (h2r : (2 ^ n).Coprime r) :
    ∑ d ∈ Nat.divisors (2 ^ n * r), d = (2 ^ (n + 1) - 1) * (r + 1) := by
  rw [h2r.sum_divisors_mul, thabit_two_pow_sigma, pr.sum_divisors]

private theorem thabit_sigma_targets (n p q r : ℕ) (hn : 2 ≤ n)
    (hp : p = 3 * 2 ^ n - 1) (hq : q = 3 * 2 ^ (n - 1) - 1)
    (hr : r = 9 * 2 ^ (2 * n - 1) - 1) :
    (2 ^ (n + 1) - 1) * (p + 1) * (q + 1) = 2 ^ n * (p * q + r) ∧
      (2 ^ (n + 1) - 1) * (r + 1) = 2 ^ n * (p * q + r) := by
  obtain ⟨hp1, hq1, hr1⟩ := thabit_parameter_successors n p q r hn hp hq hr
  obtain ⟨_, hpqr⟩ := thabit_parameter_product n p q r hn hp hq hr
  have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = 1 + (n - 1) by omega, pow_add]
    norm_num
  constructor
  · rw [hp1, hq1, hpow_n, hpqr]
    ring
  · rw [hr1, hpow_n, hpqr]
    ring

/-- **Thābit ibn Qurra's theorem.** Let $n \ge 2$ be a natural number and put $p = 3 \cdot 2^n - 1$,
$q = 3 \cdot 2^{n-1} - 1$ and $r = 9 \cdot 2^{2n-1} - 1$. If $p$, $q$ and $r$ are all prime, then
$2^n p q < 2^n r$, the sum of the proper divisors of $2^n p q$ equals $2^n r$, and the sum of the
proper divisors of $2^n r$ equals $2^n p q$; that is, $2^n p q$ and $2^n r$ are distinct amicable
numbers.

Proves `Wanted` entry `thabit_ibn_qurra`.

Proof: Following Thabit ibn Qurra's construction as recorded in Dickson, *History of the Theory
of Numbers*, Vol. I, Ch. I, p. 39, and the cited Wikipedia account, compute full divisor sums by
multiplicativity and recover the proper-divisor sums by subtracting each number.

Source: https://en.wikipedia.org/wiki/Amicable_numbers#Th%C4%81bit_ibn_Qurra_theorem
-/
theorem thabit_ibn_qurra :
    ∀ (n p q r : ℕ), 2 ≤ n →
      p = 3 * 2 ^ n - 1 →
      q = 3 * 2 ^ (n - 1) - 1 →
      r = 9 * 2 ^ (2 * n - 1) - 1 →
      Nat.Prime p → Nat.Prime q → Nat.Prime r →
      2 ^ n * p * q < 2 ^ n * r ∧
      ∑ d ∈ Nat.properDivisors (2 ^ n * p * q), d = 2 ^ n * r ∧
      ∑ d ∈ Nat.properDivisors (2 ^ n * r), d = 2 ^ n * p * q := by
  intro n p q r hn hp hq hr pp pq pr
  obtain ⟨hpq_lt, _⟩ := thabit_parameter_product n p q r hn hp hq hr
  obtain ⟨h2p, h2q, h2r, hpq⟩ := thabit_coprime_data n p q r hn hp hq hr pp pq pr
  obtain ⟨htarget_pqr, htarget_r⟩ := thabit_sigma_targets n p q r hn hp hq hr
  have hlt : 2 ^ n * p * q < 2 ^ n * r := by
    simpa [mul_assoc] using
      (Nat.mul_lt_mul_left (Nat.two_pow_pos n)).mpr hpq_lt
  have hsigma_pqr : ∑ d ∈ Nat.divisors (2 ^ n * p * q), d =
      2 ^ n * (p * q + r) :=
    (thabit_sigma_pqr n p q pp pq h2p h2q hpq).trans htarget_pqr
  have hsigma_r : ∑ d ∈ Nat.divisors (2 ^ n * r), d =
      2 ^ n * (p * q + r) :=
    (thabit_sigma_r n r pr h2r).trans htarget_r
  have hproper_pqr : ∑ d ∈ Nat.properDivisors (2 ^ n * p * q), d = 2 ^ n * r := by
    apply Nat.add_right_cancel (m := 2 ^ n * p * q)
    rw [← Nat.sum_divisors_eq_sum_properDivisors_add_self]
    calc
      ∑ d ∈ Nat.divisors (2 ^ n * p * q), d = 2 ^ n * (p * q + r) := hsigma_pqr
      _ = 2 ^ n * r + 2 ^ n * p * q := by ring
  have hproper_r : ∑ d ∈ Nat.properDivisors (2 ^ n * r), d = 2 ^ n * p * q := by
    apply Nat.add_right_cancel (m := 2 ^ n * r)
    rw [← Nat.sum_divisors_eq_sum_properDivisors_add_self]
    calc
      ∑ d ∈ Nat.divisors (2 ^ n * r), d = 2 ^ n * (p * q + r) := hsigma_r
      _ = 2 ^ n * p * q + 2 ^ n * r := by ring
  exact ⟨hlt, hproper_pqr, hproper_r⟩

end

end MetaMathlibExt
