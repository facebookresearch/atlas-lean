/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.ExponentialDerivative

@[expose] public section

open MvPowerSeries

-- The canonical exponential of one variable is its own derivative.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (i : σ) :
    pderiv i (expOfConstantCoeffZero (X i : MvPowerSeries σ R) (by simp)) =
      expOfConstantCoeffZero (X i : MvPowerSeries σ R) (by simp) := by
  rw [pderiv_expOfConstantCoeffZero, pderiv_X_self, one_mul]

-- For exp(X²), the cubic derivative coefficient is 2 and even degrees are unsupported.
example : PowerSeries.coeff 3
    (pderiv () (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply]))) = 2 := by
  change PowerSeries.coeff 3
    (PowerSeries.derivative (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply]))) = 2
  rw [PowerSeries.coeff_derivative, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_pow (by decide)]
  norm_num [PowerSeries.coeff_exp, Nat.factorial]

example : PowerSeries.coeff 2
    (pderiv () (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply]))) = 0 := by
  change PowerSeries.coeff 2
    (PowerSeries.derivative (expOfConstantCoeffZero (PowerSeries.X ^ 2 : PowerSeries ℚ)
      (by simp [PowerSeries.X_apply]))) = 0
  rw [PowerSeries.coeff_derivative, expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_pow (by decide)]
  norm_num

-- The zero exponential has zero derivative.
example : pderiv ()
    (expOfConstantCoeffZero (0 : MvPowerSeries Unit ℚ) (map_zero _)) = 0 := by
  rw [pderiv_expOfConstantCoeffZero]
  simp

-- The first finite truncation is constant, for every input.
example {σ R : Type*} [CommRing R] [Algebra ℚ R] (i : σ)
    (w : MvPowerSeries σ R) : pderiv i (expTrunc 1 w) = 0 := by
  calc
    pderiv i (expTrunc 1 w) = pderiv i w * expTrunc 0 w := pderiv_expTrunc i 0 w
    _ = 0 := by simp [expTrunc]

-- The finite law accepts a nonzero constant coefficient.
example : constantCoeff
    (pderiv () (expTrunc 3
      (PowerSeries.X + PowerSeries.C 1 : PowerSeries ℚ))) = 2 := by
  rw [pderiv_expTrunc]
  have hd : pderiv () (PowerSeries.X + PowerSeries.C 1 : PowerSeries ℚ) = 1 := by
    change PowerSeries.derivative (PowerSeries.X + PowerSeries.C 1) = 1
    rw [map_add, PowerSeries.derivative_X, PowerSeries.derivative_C, add_zero]
  rw [hd]
  simp [expTrunc, Finset.sum_range_succ, PowerSeries.X_apply]
  norm_num

-- A mixed two-variable exponential has mixed derivative coefficient one.
example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (pderiv 0 (expOfConstantCoeffZero
      (X 0 + X 1 : MvPowerSeries (Fin 2) ℚ) (by simp))) = 1 := by
  rw [pderiv_expOfConstantCoeffZero, map_add, pderiv_X_self,
    pderiv_X_of_ne (by decide), add_zero, one_mul,
    expOfConstantCoeffZero_eq_subst,
    PowerSeries.coeff_subst_X_zero_add_X_one]
  norm_num [PowerSeries.coeff_exp, Nat.factorial]

-- Transitive trusted-axiom audit of both public declarations added in the source module.
#print axioms MvPowerSeries.pderiv_expTrunc
#print axioms MvPowerSeries.pderiv_expOfConstantCoeffZero
