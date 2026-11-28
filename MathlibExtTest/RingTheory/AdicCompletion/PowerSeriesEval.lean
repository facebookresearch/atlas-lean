/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.AdicCompletion.PowerSeriesEval

/-! Tests for the evaluation of power series in an adic completion: it extends polynomial
evaluation, sends `X` to the image of the point, is multiplicative, and its image modulo `I ^ n`
is the value of the truncation. -/

open PowerSeries

variable {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I)

example : AdicCompletion.evalPowerSeries I hx PowerSeries.X = AdicCompletion.of I A x := by
  rw [← Polynomial.coe_X, AdicCompletion.evalPowerSeries_coe, Polynomial.eval_X]

example (a : A) :
    AdicCompletion.evalPowerSeries I hx (PowerSeries.C a) = AdicCompletion.of I A a := by
  rw [← Polynomial.coe_C, AdicCompletion.evalPowerSeries_coe, Polynomial.eval_C]

example (f g : A⟦X⟧) :
    AdicCompletion.evalPowerSeries I hx (f * g) =
      AdicCompletion.evalPowerSeries I hx f * AdicCompletion.evalPowerSeries I hx g :=
  map_mul _ f g

-- The geometric series `Σ Xᵏ` evaluates modulo `I ^ n` to `Σ_{k<n} xᵏ`.
example (n : ℕ) :
    AdicCompletion.evalₐ I n (AdicCompletion.evalPowerSeries I hx (PowerSeries.mk fun _ => 1)) =
      Ideal.Quotient.mk (I ^ n) (∑ k ∈ Finset.range n, x ^ k) := by
  rw [AdicCompletion.evalₐ_evalPowerSeries, Polynomial.eval, eval₂_trunc_eq_sum_range]
  simp
