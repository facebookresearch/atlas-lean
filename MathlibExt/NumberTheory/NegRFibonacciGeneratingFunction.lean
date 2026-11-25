/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.NegRFibonacciPolynomial
import Mathlib.Tactic.Ring

/-! # Generating function of the negative-order Fibonacci polynomials -/

namespace MetaMathlibExt

/-- **Generating function of the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. In the ring
$A[[z]]$ of formal power series,
$$\left(1 - y^{-1} z^r + x y^{-1} z^{r+1}\right) \sum_{n \ge 0} U_{n+1} z^n = 1.$$

The paper states the identity for complex $z$; convergence is not part of this statement.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 8 (`integers-2025-A38-thm-8`). -/
public theorem negRFibonacci_generatingFunction {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) :
    (1 - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r
        + PowerSeries.C (x * ↑y⁻¹) * PowerSeries.X ^ (r + 1)) *
      PowerSeries.mk (fun n => negRFibonacci r x y (n + 1)) = 1 := by
  apply PowerSeries.ext
  intro n
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases h : r ≤ n
  · rw [ite_eq_left h, negRFibonacci_succ_of_le x y (by omega) h,
      ite_eq_right (by omega : n ≠ 0)]
    rcases eq_or_lt_of_le h with rfl | hlt
    · simp [negRFibonacci_zero]
    · rw [ite_eq_left (Nat.succ_le_of_lt hlt), show n - (r + 1) + 1 = n - r by omega]
      ring
  · simp only [ite_eq_right h, ite_eq_right (by omega : ¬r + 1 ≤ n), mul_zero, sub_zero, add_zero]
    cases n with
    | zero => simp [negRFibonacci_one]
    | succ n => simpa using negRFibonacci_succ_of_lt x y (Nat.succ_pos n) (lt_of_not_ge h)

end MetaMathlibExt
