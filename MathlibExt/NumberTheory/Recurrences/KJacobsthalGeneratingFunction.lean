/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Tactic.Ring

/-! # Generating function of the companion k-Jacobsthal numbers -/

namespace MetaMathlibExt

/-- **Generating function of the companion $k$-Jacobsthal numbers.** For every natural number $k$
and all integers $a, b$, the companion $k$-Jacobsthal numbers $\mathcal{J}_{k,n} =
\mathcal{J}_{k,n}(a, b)$ satisfy, in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} \mathcal{J}_{k,n} x^n\Bigr)(1 - kx - 2x^2) = a + (b - ak)x.$$

This is the identity $\sum_{n \ge 0} \mathcal{J}_{k,n} x^n = \frac{a + (b - ak)x}{1 - kx - 2x^2}$
with the denominator cleared.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 10 (`integers-2025-A74-thm-10`). -/
public theorem companionKJacobsthal_generatingFunction (k : ℕ) (a b : ℤ) :
    PowerSeries.mk (companionKJacobsthal k a b) *
        (1 - PowerSeries.C (k : ℤ) * PowerSeries.X - PowerSeries.C 2 * PowerSeries.X ^ 2) =
      PowerSeries.C a + PowerSeries.C (b - a * k) * PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  simp only [mul_sub, mul_one, pow_two, ← mul_assoc,
    map_sub (PowerSeries.coeff (R := ℤ) n), map_add (PowerSeries.coeff (R := ℤ) n)]
  rcases n with _ | _ | n
  · simp only [PowerSeries.coeff_mk, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C,
      companionKJacobsthal, sub_zero, add_zero]
  · simp only [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mk, PowerSeries.coeff_zero_C, PowerSeries.coeff_succ_C,
      companionKJacobsthal, sub_zero, zero_add]
  · simp only [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk,
      PowerSeries.coeff_succ_C, add_zero]
    rw [companionKJacobsthal_add_two]
    ring

end MetaMathlibExt
