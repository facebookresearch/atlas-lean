/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/BergerBst.lean` and
`ZInQKernel/Contrib/OneProof/FontaineLogCore.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.PowerSeriesEval

/-!
# Values of power series in an adic completion

Further properties of the evaluation `AdicCompletion.evalPowerSeries I hx : A⟦X⟧ →+* Â_I` at an
element `x ∈ I`: the values of constants and of `X`, and a criterion for two series to have the
same value (`AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq`).
-/

@[expose] public noncomputable section

open PowerSeries

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A) {x : A}

/-- For an ideal `I` of a commutative ring `A` and `x ∈ I`, the value at `x` of a constant series
`C a` is the image of `a` in the `I`-adic completion. -/
@[simp]
theorem evalPowerSeries_C (hx : x ∈ I) (a : A) : evalPowerSeries I hx (C a) = of I A a := by
  rw [← Polynomial.coe_C, evalPowerSeries_coe, Polynomial.eval_C]

/-- For an ideal `I` of a commutative ring `A` and `x ∈ I`, the value at `x` of `X` is the image
of `x` in the `I`-adic completion. -/
@[simp]
theorem evalPowerSeries_X (hx : x ∈ I) : evalPowerSeries I hx X = of I A x := by
  rw [← Polynomial.coe_X, evalPowerSeries_coe, Polynomial.eval_X]

/-- For an ideal `I` of a commutative ring `A`, two series `f = Σ aₖ Xᵏ` and `g = Σ bₖ Xᵏ` over
`A` have the same values at `x ∈ I` and at `y ∈ I` if their terms agree: `aₖ xᵏ = bₖ yᵏ` for
every `k`. -/
theorem evalPowerSeries_eq_of_coeff_mul_pow_eq {y : A} (hx : x ∈ I) (hy : y ∈ I) (f g : A⟦X⟧)
    (h : ∀ k, coeff k f * x ^ k = coeff k g * y ^ k) :
    evalPowerSeries I hx f = evalPowerSeries I hy g :=
  ext_evalₐ fun n => by
    rw [evalₐ_evalPowerSeries, evalₐ_evalPowerSeries, Polynomial.eval, Polynomial.eval,
      eval₂_trunc_eq_sum_range, eval₂_trunc_eq_sum_range]
    simp only [RingHom.id_apply, h]

end AdicCompletion
