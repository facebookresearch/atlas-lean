/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/PDeriv.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
port the exponential derivative laws to the canonical formal exponential API.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.Exponential
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Derivatives of multivariate formal exponentials

The partial derivative of the finite exponential sum containing the terms `w ^ n / n!` for
`n ≤ N` is the derivative of its exponent times the sum containing those terms for `n < N`.
For a series with zero constant coefficient, the same identity holds for the canonical formal
exponential.
-/

@[expose] public section

namespace MvPowerSeries

open Finset

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

private theorem inv_factorial_succ_mul (n : ℕ) :
    (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) = (n.factorial : ℚ)⁻¹ := by
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- The partial derivative of the finite exponential sum containing the terms `w ^ n / n!` for
`n ≤ N` is the derivative of its exponent times the sum containing those terms for `n < N`. -/
theorem pderiv_expTrunc (i : σ) (N : ℕ) (w : MvPowerSeries σ R) :
    pderiv i (expTrunc (N + 1) w) = pderiv i w * expTrunc N w := by
  unfold expTrunc
  rw [sum_range_succ', map_add, map_sum, mul_sum]
  have h0 : pderiv i (((Nat.factorial 0 : ℚ)⁻¹) • w ^ 0) = 0 := by
    rw [map_rat_smul, pow_zero, pderiv_one, smul_zero]
  rw [h0, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [map_rat_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_factorial_succ_mul,
    mul_smul_comm, mul_comm]

/-- The partial derivative of the canonical exponential is the derivative of its exponent times
the exponential. -/
theorem pderiv_expOfConstantCoeffZero (i : σ) {w : MvPowerSeries σ R}
    (hw : constantCoeff w = 0) :
    pderiv i (expOfConstantCoeffZero w hw) =
      pderiv i w * expOfConstantCoeffZero w hw := by
  classical
  ext d
  have hdegree : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [coeff_pderiv,
    coeff_expOfConstantCoeffZero w hw (d + Finsupp.single i 1)
      (N := d.degree + 1 + 1) (by rw [hdegree]; omega),
    ← coeff_pderiv, pderiv_expTrunc, coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have hpdegree := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at hpdegree
  rw [← coeff_expOfConstantCoeffZero w hw p.2 (N := d.degree + 1) (by omega)]

end MvPowerSeries
