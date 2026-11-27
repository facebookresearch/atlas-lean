/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/BergerBst.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

/-!
# Evaluating a power series in an adic completion

Let `I` be an ideal of a commutative ring `A` and let `x ∈ I`. A power series `f = Σ aₖ Xᵏ` over
`A` has a value at `x` in the `I`-adic completion of `A`: modulo `I ^ n`, the terms of degree at
least `n` vanish, so the truncations `Σ_{k<n} aₖ xᵏ` form an `I`-adic Cauchy sequence.
`AdicCompletion.evalPowerSeries` is the resulting ring homomorphism `A⟦X⟧ →+* AdicCompletion I A`.
It extends the evaluation of polynomials (`AdicCompletion.evalPowerSeries_coe`).

This evaluation is used for series in the divided powers of a generator of the kernel of
Fontaine's map `θ`, in the sense of Fontaine, *Le corps des périodes p-adiques*, Astérisque 223
(1994), Exposé II, §2.3.3 p. 78 and §4.1.2 p. 83.

## Main definitions

* `AdicCompletion.evalPowerSeries`: evaluation `A⟦X⟧ →+* AdicCompletion I A` at `x ∈ I`.

## Main results

* `AdicCompletion.evalₐ_evalPowerSeries`: modulo `I ^ n`, the value of `f` is the value of its
  truncation below degree `n`.
* `AdicCompletion.evalPowerSeries_coe`: on polynomials, the evaluation is the usual one.
-/

@[expose] public noncomputable section

open PowerSeries

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A) {x : A}

private theorem eval_mem_pow_of_coeff (hx : x ∈ I) (n : ℕ) (Q : Polynomial A)
    (hQ : ∀ k < n, Q.coeff k = 0) : Q.eval x ∈ I ^ n := by
  have hdvd : (Polynomial.X : Polynomial A) ^ n ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    exact hQ
  obtain ⟨R, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

/-- `P(x) ≡ (P mod X^n)(x) mod I^n`. -/
private theorem eval_sub_trunc_mem (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    P.eval x - (trunc n (P : A⟦X⟧)).eval x ∈ I ^ n := by
  rw [← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hk, Polynomial.coeff_coe, sub_self]

/-- For `x ∈ I`, the values at `x` of the truncations of a power series below degrees `n` and
`n + 1` are congruent modulo `I ^ n`. -/
theorem eval_trunc_smodEq_eval_trunc_succ (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    (trunc n f).eval x ≡ (trunc (n + 1) f).eval x [SMOD (I ^ n • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, ite_eq_left hk, ite_eq_left (by omega),
    sub_self]

private theorem mk_eval_trunc (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    Ideal.Quotient.mk (I ^ n) ((trunc n (P : A⟦X⟧)).eval x) =
      Ideal.Quotient.mk (I ^ n) (P.eval x) := by
  rw [Ideal.Quotient.eq]
  have := eval_sub_trunc_mem I hx n P
  rw [← neg_sub]
  exact Submodule.neg_mem _ this

/-- Evaluation of power series over `A` at an element `x ∈ I`, with values in the `I`-adic
completion of `A`: the series `Σ aₖ Xᵏ` is sent to the element whose image in `A ⧸ I ^ n` is the
class of `Σ_{k<n} aₖ xᵏ`, for every `n` (`AdicCompletion.evalₐ_evalPowerSeries`). -/
def evalPowerSeries (hx : x ∈ I) : A⟦X⟧ →+* AdicCompletion I A where
  toFun f := AdicCompletion.mk I A (AdicCompletion.AdicCauchySequence.mk I A
    (fun n => (trunc n f).eval x) (eval_trunc_smodEq_eval_trunc_succ I hx f))
  map_one' := AdicCompletion.ext_evalₐ fun n => by
    rw [AdicCompletion.evalₐ_mk, map_one (AdicCompletion.evalₐ I n)]
    change Ideal.Quotient.mk (I ^ n) ((trunc n 1).eval x) = 1
    rw [← Polynomial.coe_one, mk_eval_trunc I hx, Polynomial.eval_one, map_one]
  map_mul' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [AdicCompletion.evalₐ_mk, map_mul (AdicCompletion.evalₐ I n), AdicCompletion.evalₐ_mk,
      AdicCompletion.evalₐ_mk]
    change Ideal.Quotient.mk (I ^ n) ((trunc n (f * g)).eval x) =
      Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) *
        Ideal.Quotient.mk (I ^ n) ((trunc n g).eval x)
    rw [← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, mk_eval_trunc I hx, Polynomial.eval_mul,
      map_mul]
  map_zero' := AdicCompletion.ext_evalₐ fun n => by
    rw [AdicCompletion.evalₐ_mk, map_zero (AdicCompletion.evalₐ I n)]
    change Ideal.Quotient.mk (I ^ n) ((trunc n 0).eval x) = 0
    rw [map_zero (trunc n), Polynomial.eval_zero, map_zero]
  map_add' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [AdicCompletion.evalₐ_mk, map_add (AdicCompletion.evalₐ I n), AdicCompletion.evalₐ_mk,
      AdicCompletion.evalₐ_mk]
    change Ideal.Quotient.mk (I ^ n) ((trunc n (f + g)).eval x) =
      Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) +
        Ideal.Quotient.mk (I ^ n) ((trunc n g).eval x)
    rw [map_add (trunc n), Polynomial.eval_add, map_add]

/-- Modulo `I ^ n`, the value at `x ∈ I` of a power series `f` is the value at `x` of its
truncation `trunc n f` below degree `n`. -/
theorem evalₐ_evalPowerSeries (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (evalPowerSeries I hx f) =
      Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) := by
  change AdicCompletion.evalₐ I n (AdicCompletion.mk I A _) = _
  rw [AdicCompletion.evalₐ_mk]
  rfl

/-- On a polynomial `P`, viewed as a power series, evaluation at `x ∈ I` is the image of
`P.eval x` in the `I`-adic completion. -/
theorem evalPowerSeries_coe (hx : x ∈ I) (P : Polynomial A) :
    evalPowerSeries I hx (P : A⟦X⟧) = AdicCompletion.of I A (P.eval x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_evalPowerSeries, mk_eval_trunc I hx, AdicCompletion.evalₐ_of]

end AdicCompletion
