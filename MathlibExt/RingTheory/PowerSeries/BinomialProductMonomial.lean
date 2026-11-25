/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import MathlibExt.RingTheory.PowerSeries.BinomialProduct

/-!
# Binomial product with a monomial

In degree `n`, the monomial `X ^ m` selects the term with index `m` in the binomial convolution.
The coefficient formula for the iterated formal derivative gives the same binomial factor.
-/

namespace MetaMathlibExt

open PowerSeries

/-- **Binomial product with a monomial.** For every field $K$ of characteristic $0$, every
$m \in \mathbb{N}$ and every power series $A(x)$ over $K$,

$$x^m \odot A(x) = \frac{x^m}{m!} \frac{d^m}{dx^m}\bigl(x^m A(x)\bigr),$$

where $\odot$ is the binomial product and $d/dx$ is the formal derivative.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 8 (`jis-2024-24.1.3-lem-8`). -/
public theorem binomialProduct_X_pow {K : Type*} [Field K] [CharZero K] (m : ℕ)
    (A : PowerSeries K) :
    binomialProduct (X ^ m) A =
      C ((m.factorial : K)⁻¹) * X ^ m * (⇑(PowerSeries.derivative (R := K)))^[m] (X ^ m * A) := by
  ext n
  rw [coeff_binomialProduct, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [coeff_X_pow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range_succ_iff]
  split_ifs with h
  · rw [coeff_iterate_derivative, coeff_X_pow_mul, Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.sub_add_cancel h, Nat.cast_mul]
    simp [mul_assoc, Nat.factorial_ne_zero]
  · rfl

end MetaMathlibExt
