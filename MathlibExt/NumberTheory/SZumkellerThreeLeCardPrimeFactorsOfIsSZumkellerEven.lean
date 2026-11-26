/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SZumkeller
import MathlibExt.NumberTheory.SumSquaredDivisorsProduct

/-!
# Even s-Zumkeller numbers have at least three prime factors

If `n` is an even s-Zumkeller number, then `n` has at least three distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(i).
-/

namespace MetaMathlibExt

/-- If `n` is an even s-Zumkeller number and `σ₂(n)` is the sum of the squares of the positive
divisors of `n`, then `3n² ≤ 2σ₂(n)`. -/
private theorem three_mul_sq_le_of_isSZumkeller_even (n : ℕ) (h : IsSZumkeller n)
    (he : Even n) : 3 * (n : ℚ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n := by
  obtain ⟨A, hA, hne, hcompl, hbal⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hne.mono hA)
  have hn : 0 < n := by omega
  obtain ⟨S, _, hS⟩ := (isSZumkeller_iff_of_even n hn he).mp ⟨A, hA, hne, hcompl, hbal⟩
  have hnonneg : 0 ≤ ∑ d ∈ S, (d : ℤ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact_mod_cast (show 3 * (n : ℤ) ^ 2 ≤ 2 * ArithmeticFunction.sigma 2 n by omega)

/-- For `p ≥ 3`, `p² / (p² - 1) ≤ 9 / 8`. -/
private theorem sq_div_sub_one_le_of_three_le (p : ℕ) (hp : 3 ≤ p) :
    (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) ≤ 9 / 8 := by
  have hp3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hden : (0 : ℚ) < (p : ℚ) ^ 2 - 1 := by nlinarith [hp3]
  rw [div_le_div_iff₀ hden (by norm_num)]
  nlinarith [hp3, sq_nonneg ((p : ℚ) - 3)]

/-- If `2` is a prime factor of `n` and `n` has at most two distinct prime factors, then the
product of `p² / (p² - 1)` over the prime factors `p` of `n` is at most `3 / 2`. -/
private theorem prod_le_of_card_le_two (n : ℕ) (h2 : 2 ∈ n.primeFactors)
    (hcard : n.primeFactors.card ≤ 2) :
    ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) ≤ 3 / 2 := by
  have hcardT : (n.primeFactors.erase 2).card ≤ 1 := by
    rw [Finset.card_erase_of_mem h2]
    omega
  rw [← Finset.mul_prod_erase _ _ h2]
  have hf2 : ((2 : ℕ) : ℚ) ^ 2 / (((2 : ℕ) : ℚ) ^ 2 - 1) = 4 / 3 := by norm_num
  rw [hf2]
  have hcases : (n.primeFactors.erase 2).card = 0 ∨ (n.primeFactors.erase 2).card = 1 := by
    omega
  rcases hcases with h0 | h1
  · have hempty : n.primeFactors.erase 2 = ∅ := Finset.card_eq_zero.mp h0
    rw [hempty, Finset.prod_empty, mul_one]
    norm_num
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    rw [hp, Finset.prod_singleton]
    have hpT : p ∈ n.primeFactors.erase 2 := by
      rw [hp]
      exact Finset.mem_singleton_self p
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hpT
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hp3 : 3 ≤ p := by
      have h2le := hprime.two_le
      omega
    have hfp := sq_div_sub_one_le_of_three_le p hp3
    calc (4 : ℚ) / 3 * ((p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1))
        ≤ 4 / 3 * (9 / 8) := mul_le_mul_of_nonneg_left hfp (by norm_num)
      _ = 3 / 2 := by norm_num

/-- **Even s-Zumkeller numbers have at least three prime factors.** If $n$ is an even
s-Zumkeller number, then $n$ has at least $3$ distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(i). -/
public theorem three_le_card_primeFactors_of_isSZumkeller_even (n : ℕ)
    (h : IsSZumkeller n) (he : Even n) : 3 ≤ n.primeFactors.card := by
  obtain ⟨A, hA, hne, hcompl, hbal⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hne.mono hA)
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, he.two_dvd, hn0⟩
  have hlower :=
    three_mul_sq_le_of_isSZumkeller_even n ⟨A, hA, hne, hcompl, hbal⟩ he
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) 2
  have hupper := (sigma_two_prod_formulas n hn0).2.2 hn1
  have hle : (3 : ℚ) / 2 ≤ (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 := by
    rw [le_div_iff₀ hpos]
    linarith [hlower]
  by_contra hcard
  have hsmall := prod_le_of_card_le_two n h2 (by omega)
  have hlt := lt_of_le_of_lt hle hupper
  linarith [hlt, hsmall]

end MetaMathlibExt
