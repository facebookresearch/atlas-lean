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

/-- **Even s-Zumkeller numbers have at least three prime factors.** If $n$ is an even
s-Zumkeller number, then $n$ has at least $3$ distinct prime factors.

Source: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 6(i). -/
public theorem three_le_card_primeFactors_of_isSZumkeller_even (n : ℕ)
    (h : IsSZumkeller n) (he : Even n) : 3 ≤ n.primeFactors.card := by
  obtain ⟨A, hA, hne, hcompl, hbal⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hne.mono hA)
  have hn0 : n ≠ 0 := by omega
  have h3 : 3 ∣ n := three_dvd_of_isSZumkeller n ⟨A, hA, hne, hcompl, hbal⟩ he
  have hsub : ({2, 3} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, he.two_dvd, hn0⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hn0⟩
  have hlower :=
    three_mul_sq_le_of_isSZumkeller_even n ⟨A, hA, hne, hcompl, hbal⟩ he
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) 2
  have hupper := (sigma_two_prod_formulas n hn0).2.2 hn1
  have hle : (3 : ℚ) / 2 ≤ (ArithmeticFunction.sigma 2 n : ℚ) / (n : ℚ) ^ 2 := by
    rw [le_div_iff₀ hpos]
    linarith [hlower]
  by_contra hcard
  have heq : ({2, 3} : Finset ℕ) = n.primeFactors :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair (by decide)]; omega)
  rw [← heq, Finset.prod_pair (by decide)] at hupper
  norm_num at hupper
  linarith

end MetaMathlibExt
