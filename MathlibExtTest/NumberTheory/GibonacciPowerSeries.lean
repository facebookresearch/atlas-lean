/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPowerSeries

namespace MetaMathlibExt

open PowerSeries

private noncomputable def scaledSeries (a b : ℤ) : PowerSeries ℚ :=
  (1 - X - X ^ 2) * mk (fun n => (gibonacciNumber a b n : ℚ))

example (a b : ℤ) : coeff 0 (scaledSeries a b) = (a : ℚ) := by
  rw [scaledSeries, gibonacci_powerSeries_mul (b := b) (a := a)]
  simp only [map_add, coeff_C_mul, coeff_C, coeff_X]
  simp

example (a b : ℤ) : coeff 1 (scaledSeries a b) = (b : ℚ) - (a : ℚ) := by
  rw [scaledSeries, gibonacci_powerSeries_mul (b := b) (a := a)]
  simp only [map_add, coeff_C_mul, coeff_C, coeff_X]
  simp

example (a b : ℤ) (n : ℕ) : coeff (n + 2) (scaledSeries a b) = 0 := by
  rw [scaledSeries, gibonacci_powerSeries_mul (b := b) (a := a)]
  simp only [map_add, coeff_C_mul, coeff_C, coeff_X]
  simp

#print axioms gibonacci_powerSeries_mul

end MetaMathlibExt
