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
# A prime-factor product bound for s-Zumkeller numbers

For an s-Zumkeller number `n` with least prime factor `p₁`,
`2 / p₁ ^ 2 + 1 < ∏ p ∈ n.primeFactors, p ^ 2 / (p ^ 2 - 1)`
(Kalita–Saikia, Proposition 5). The proof bounds the normalized sum of squared
divisors below by the least-prime-factor expression and, strictly, above by the
prime-factor product from `sigma_two_prod_formulas`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **A prime-factor product bound for s-Zumkeller numbers.** Let $n$ be an s-Zumkeller number
and let $p_1$ be its least prime factor. Then
$$\frac{2}{p_1^2} + 1 < \prod_{p} \frac{p^2}{p^2 - 1},$$
where the product ranges over the distinct prime factors $p$ of $n$.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 5. -/
public theorem two_div_minFac_sq_add_one_lt_prod (n : ℕ) (h : IsSZumkeller n) :
    2 / (n.minFac : ℚ) ^ 2 + 1 < ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
  obtain ⟨A, hA, hneA, _, hbal⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hneA.mono hA)
  have hn0 : n ≠ 0 := by omega
  have hprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hmem : n / n.minFac ∈ n.properDivisors := Nat.mem_properDivisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd n), Nat.div_lt_self (by omega) hprime.one_lt⟩
  have hsq : (n / n.minFac) ^ 2 ≤ ∑ d ∈ A, d ^ 2 := by
    by_cases hmA : n / n.minFac ∈ A
    · exact Finset.single_le_sum (f := fun d : ℕ => d ^ 2) (fun _ _ => Nat.zero_le _)
        hmA
    · have hmB : n / n.minFac ∈ n.properDivisors \ A := Finset.mem_sdiff.mpr ⟨hmem, hmA⟩
      have hle := Finset.single_le_sum (f := fun d : ℕ => d ^ 2) (fun _ _ => Nat.zero_le _)
        hmB
      simpa only [hbal] using hle
  have hσ : ArithmeticFunction.sigma 2 n = n ^ 2 + ∑ d ∈ n.properDivisors, d ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, ← Nat.insert_self_properDivisors hn0,
      Finset.sum_insert Nat.self_notMem_properDivisors]
  have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d ^ 2) hA
  have hbound : n ^ 2 + 2 * (n / n.minFac) ^ 2 ≤ ArithmeticFunction.sigma 2 n := by
    omega
  have hdiv : n / n.minFac * n.minFac = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  have hm0 : n / n.minFac ≠ 0 := by
    intro hz
    exact hn0 (by rw [← hdiv, hz, zero_mul])
  have hnpos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnpos2 : (0 : ℚ) < (n : ℚ) ^ 2 := pow_pos hnpos 2
  have hcast : (n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2 ≤
      (ArithmeticFunction.sigma 2 n : ℚ) := by
    exact_mod_cast hbound
  have hle : ((n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2) / (n : ℚ) ^ 2 ≤
      (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 :=
    (div_le_div_iff_of_pos_right hnpos2).mpr hcast
  have hN : (n : ℚ) = ((n / n.minFac : ℕ) : ℚ) * (n.minFac : ℚ) := by
    exact_mod_cast hdiv.symm
  have hM : ((n / n.minFac : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hP : (n.minFac : ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hident : ((n : ℚ) ^ 2 + 2 * ((n / n.minFac : ℕ) : ℚ) ^ 2) / (n : ℚ) ^ 2 =
      2 / (n.minFac : ℚ) ^ 2 + 1 := by
    rw [hN, mul_pow]
    have e1 : (((n / n.minFac : ℕ) : ℚ) ^ 2 * (n.minFac : ℚ) ^ 2 +
        2 * ((n / n.minFac : ℕ) : ℚ) ^ 2) =
        ((n / n.minFac : ℕ) : ℚ) ^ 2 * ((n.minFac : ℚ) ^ 2 + 2) := by ring
    rw [e1, mul_div_mul_left _ _ (pow_ne_zero 2 hM), add_div,
      div_self (pow_ne_zero 2 hP), add_comm]
  have hstrict : (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 <
      ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1) :=
    (sigma_two_prod_formulas n hn0).2.2 hn1
  rw [← hident]
  exact lt_of_le_of_lt hle hstrict

end

end MetaMathlibExt
