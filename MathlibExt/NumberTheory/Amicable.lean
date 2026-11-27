/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Field

/-!
# Divisor sums and amicable numbers

Following Stoyan Dimitrov's *Generalizations of Amicable Numbers*, we bound the sum of the
abundancy indices by counting multiples of each divisor.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.AmicableWanted

open Finset

private theorem sigma_div_eq_sum_reciprocals (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  rw [ArithmeticFunction.sigma_eq_sum_div, Nat.cast_sum, Finset.sum_div]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [pow_one, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0, div_right_comm, div_self]
  exact_mod_cast hn.ne'

private theorem sum_reciprocal_squares_lt (N : ℕ) :
    ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2 < ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2 := by
  have hs := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by decide)
  calc
    _ < ∑ d ∈ Ioc 0 (N + 1), 1 / (d : ℝ) ^ 2 := by
      rw [sum_Ioc_succ_top (Nat.zero_le N)]
      simp only [lt_add_iff_pos_right, Nat.cast_add_one]
      positivity
    _ ≤ ∑' d : ℕ, 1 / (d : ℝ) ^ 2 := hs.sum_le_tsum _ fun _ _ ↦ by positivity
    _ = _ := by simpa using hs.tsum_eq_zero_add

/-- **Linear bound for the partial sums of the abundancy index.** For a positive integer
$n$ let $\sigma(n)$ denote the sum of the positive divisors of $n$, and let
$\zeta(2) = \sum_{n=1}^{\infty} 1/n^2$. Then for every real number $x \ge 1$,
$$\sum_{n=1}^{\lfloor x \rfloor} \frac{\sigma(n)}{n} < \zeta(2)\, x.$$

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 2. -/
theorem sum_sigma_div_lt (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.sigma 1 n : ℝ) / n <
      (∑' n : ℕ, (1 : ℝ) / (n + 1) ^ 2) * x := by
  let N := ⌊x⌋₊
  have hN : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [show Icc 1 ⌊x⌋₊ = Ioc 0 N from Icc_add_one_left_eq_Ioc 0 N]
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, 1 / (d : ℝ) :=
      sum_congr rfl fun n hn ↦ sigma_div_eq_sum_reciprocals n (mem_Ioc.mp hn).1
    _ = ∑ d ∈ Ioc 0 N, ∑ _n ∈ (Ioc 0 N).filter (d ∣ ·), 1 / (d : ℝ) := by
      apply sum_comm'
      intro n d
      simp only [mem_Ioc, mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hn, hnN⟩, hd, _⟩
        exact ⟨⟨⟨hn, hnN⟩, hd⟩, Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hnN⟩
      · rintro ⟨⟨⟨hn, hnN⟩, hd⟩, _⟩
        exact ⟨⟨hn, hnN⟩, hd, hn.ne'⟩
    _ = ∑ d ∈ Ioc 0 N, ((N / d : ℕ) : ℝ) / d := by
      simp [Nat.Ioc_filter_dvd_card_eq_div, div_eq_mul_inv]
    _ ≤ ∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2 * x := by
      refine sum_le_sum fun d _ ↦ ?_
      calc
        _ ≤ (x / d) / d := by
          gcongr
          exact Nat.cast_div_le.trans (by gcongr)
        _ = _ := by ring
    _ = (∑ d ∈ Ioc 0 N, 1 / (d : ℝ) ^ 2) * x := (sum_mul ..).symm
    _ < _ := mul_lt_mul_of_pos_right (sum_reciprocal_squares_lt N) (by linarith)

/-- The number `M(x)` of `(α, β)`-multiamicable pairs
`m < n` with `m ≤ x`: `σ(m) = σ(n) = αm + βn`.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Section 3 (definition of multiamicable tuples) and
Theorem 5. -/
noncomputable def multiamicablePairCount (α β x : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ // 0 < p.1 ∧ p.1 ≤ x ∧ p.1 < p.2 ∧
    ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2 ∧
    ArithmeticFunction.sigma 1 p.1 = α * p.1 + β * p.2}

/-- `M(0) = 0` (no `m` with `0 < m ≤ 0`).

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Journal of Integer Sequences 28 (2025), Article
25.4.2, Theorem 5. -/
theorem multiamicablePairCount_zero (α β : ℕ) : multiamicablePairCount α β 0 = 0 := by
  rw [multiamicablePairCount, Nat.card_eq_zero]
  left
  exact ⟨fun p => by omega⟩

end MathlibExt.NumberTheory.AmicableWanted
