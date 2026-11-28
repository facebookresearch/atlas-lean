/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Comparing `ψ` with its logarithmic mean

The logarithmically weighted Chebyshev function `ψ₁(x) = ∑_{n ≤ x} Λ(n) log (x / n)` (which
equals `∫_1^x ψ(t) dt / t`) is related to `ψ` itself by two elementary sandwich inequalities:
for `1 ≤ w ≤ x`,
`ψ(w) log (x / w) ≤ ψ₁(x) - ψ₁(w) ≤ ψ(x) log (x / w)`.
They are the standard device for passing from an asymptotic formula for `ψ₁` to one for `ψ`.

## Main statements

* `Chebyshev.psi_mul_log_div_le_sub`: `ψ(x) log (y / x) ≤ ψ₁(y) - ψ₁(x)` for `1 ≤ x ≤ y`.
* `Chebyshev.sub_le_psi_mul_log_div`: `ψ₁(x) - ψ₁(w) ≤ ψ(x) log (x / w)` for `1 ≤ w ≤ x`.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

namespace Chebyshev

/-- For `1 ≤ x ≤ y`, with `ψ₁(t) = ∑_{n ≤ t} Λ(n) log (t / n)`,
`ψ(x) log (y / x) ≤ ψ₁(y) - ψ₁(x)`. -/
theorem psi_mul_log_div_le_sub {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ψ x * Real.log (y / x)
      ≤ (∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * Real.log (y / n))
        - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  have hNM : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  rw [← sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) hNM]
  -- The head sum is `ψ (x) * log (y / x)`.
  have hhead : (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (y / n))
      - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) = ψ x * Real.log (y / x) := by
    rw [Chebyshev.psi, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    rw [Real.log_div hy0.ne' hn0.ne', Real.log_div hx0.ne' hn0.ne',
      Real.log_div hy0.ne' hx0.ne']
    ring
  -- The tail sum is nonnegative.
  have htail : 0 ≤ ∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, Λ n * Real.log (y / n) := by
    refine sum_nonneg fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn2) (Nat.floor_le hy0.le)
    refine mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_nonneg ?_)
    rw [le_div_iff₀ hn0]
    linarith
  linarith

/-- For `1 ≤ w ≤ x`, with `ψ₁(t) = ∑_{n ≤ t} Λ(n) log (t / n)`,
`ψ₁(x) - ψ₁(w) ≤ ψ(x) log (x / w)`. -/
theorem sub_le_psi_mul_log_div {w x : ℝ} (hw : 1 ≤ w) (hwx : w ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n))
        - ∑ n ∈ Ioc 0 ⌊w⌋₊, Λ n * Real.log (w / n)
      ≤ ψ x * Real.log (x / w) := by
  have hw0 : (0 : ℝ) < w := lt_of_lt_of_le zero_lt_one hw
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hw0 hwx
  have hNM : ⌊w⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hwx
  rw [← sum_Ioc_consecutive _ (Nat.zero_le ⌊w⌋₊) hNM]
  -- The head sum is `ψ (w) * log (x / w)`.
  have hhead : (∑ n ∈ Ioc 0 ⌊w⌋₊, Λ n * Real.log (x / n))
      - ∑ n ∈ Ioc 0 ⌊w⌋₊, Λ n * Real.log (w / n) = ψ w * Real.log (x / w) := by
    rw [Chebyshev.psi, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    rw [Real.log_div hx0.ne' hn0.ne', Real.log_div hw0.ne' hn0.ne',
      Real.log_div hx0.ne' hw0.ne']
    ring
  -- The tail sum is at most `(ψ (x) - ψ (w)) * log (x / w)`.
  have hsplit : (∑ n ∈ Ioc ⌊w⌋₊ ⌊x⌋₊, Λ n) = ψ x - ψ w := by
    rw [Chebyshev.psi, Chebyshev.psi, ← sum_Ioc_consecutive _ (Nat.zero_le ⌊w⌋₊) hNM]
    ring
  have htail : (∑ n ∈ Ioc ⌊w⌋₊ ⌊x⌋₊, Λ n * Real.log (x / n))
      ≤ ψ x * Real.log (x / w) - ψ w * Real.log (x / w) := by
    have hbound : (∑ n ∈ Ioc ⌊w⌋₊ ⌊x⌋₊, Λ n * Real.log (x / n))
        ≤ ∑ n ∈ Ioc ⌊w⌋₊ ⌊x⌋₊, Λ n * Real.log (x / w) := by
      refine sum_le_sum fun n hn => ?_
      obtain ⟨hn1, -⟩ := mem_Ioc.mp hn
      have hnw : w ≤ (n : ℝ) := by
        have hstep : ((⌊w⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith [Nat.lt_floor_add_one w]
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hw0 hnw
      refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
      exact Real.log_le_log (div_pos hx0 hn0) (by gcongr)
    rw [← sum_mul, hsplit] at hbound
    linarith [hbound]
  linarith [hhead, htail]

end Chebyshev
