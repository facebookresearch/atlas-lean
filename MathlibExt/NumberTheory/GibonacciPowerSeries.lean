/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.GibonacciNumber

/-! # The formal generating series of a Gibonacci sequence -/

namespace MetaMathlibExt

@[expose] public section

/-- **Generating series of a Gibonacci sequence.** Let $a$ and $b$ be integers and let
$(G_n)_{n \ge 0}$ be the Gibonacci sequence with $G_0 = a$ and $G_1 = b$. In the ring
$\mathbb{Q}[[X]]$ of formal power series with rational coefficients,

$$(1 - X - X^2) \sum_{n \ge 0} G_n X^n = a + (b - a) X.$$

This is the product form of the quotient $\frac{(b - a)x + a}{1 - x - x^2}$ for the generating
function of $(G_n)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacci_powerSeries_mul (a b : ℤ) :
    (1 - PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ)
        * PowerSeries.mk (fun n => ((gibonacciNumber a b n : ℤ) : ℚ))
      = PowerSeries.C (a : ℚ)
        + PowerSeries.C ((b : ℚ) - (a : ℚ)) * PowerSeries.X := by
  rw [sub_mul, sub_mul, one_mul, pow_two, mul_assoc]
  apply PowerSeries.ext
  intro n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_C]
  rcases n with _ | _ | n
  · simp [gibonacciNumber]
  · simp [gibonacciNumber]
  · simp [gibonacciNumber, Int.cast_add]

end

end MetaMathlibExt
