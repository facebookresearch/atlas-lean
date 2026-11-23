/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Taylor.lean and Coeff.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
package the source's formal linear form as a linear map for arbitrary variable
families and prove its canonical coefficient, derivative, and mapping laws.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Formal linear forms in multivariate power series

An arbitrary coefficient family `b : σ → R` determines the formal linear form
`∑ i, b i X i`. This notation is coefficientwise: no finiteness or convergence
assumption is imposed on `σ` or `b`, because each monomial has finite support.
-/

@[expose] public section

namespace MvPowerSeries

/-- The formal linear form with variable coefficient family `b : σ → R`.

Its coefficient at `d` is the sum of `b i` over the support of `d` when `d`
has total degree one, and zero otherwise. -/
noncomputable def linearForm {σ R : Type*} [CommSemiring R] :
    (σ → R) →ₗ[R] MvPowerSeries σ R where
  toFun b d := if d.degree = 1 then ∑ i ∈ d.support, b i else 0
  map_add' b c := by
    ext d
    change (if d.degree = 1 then ∑ i ∈ d.support, (b i + c i) else 0) =
      (if d.degree = 1 then ∑ i ∈ d.support, b i else 0) +
        if d.degree = 1 then ∑ i ∈ d.support, c i else 0
    by_cases h : d.degree = 1
    · simp only [ite_eq_left h, Finset.sum_add_distrib]
    · simp only [ite_eq_right h, zero_add]
  map_smul' r b := by
    ext d
    change (if d.degree = 1 then ∑ i ∈ d.support, r * b i else 0) =
      r * if d.degree = 1 then ∑ i ∈ d.support, b i else 0
    by_cases h : d.degree = 1
    · simp only [ite_eq_left h, Finset.mul_sum]
    · simp only [ite_eq_right h, mul_zero]

/-- The coefficient formula defining a formal linear form. -/
@[simp] theorem coeff_linearForm {σ R : Type*} [CommSemiring R]
    (b : σ → R) (d : σ →₀ ℕ) :
    coeff d (linearForm b) =
      if d.degree = 1 then ∑ i ∈ d.support, b i else 0 := rfl

/-- The coefficient of variable `i` is the prescribed coefficient `b i`. -/
@[simp] theorem coeff_linearForm_single {σ R : Type*} [CommSemiring R]
    (b : σ → R) (i : σ) :
    coeff (Finsupp.single i 1) (linearForm b) = b i := by
  classical
  simp [Finsupp.degree_single]

/-- A formal linear form has zero constant coefficient. -/
@[simp] theorem constantCoeff_linearForm {σ R : Type*} [CommSemiring R]
    (b : σ → R) : constantCoeff (linearForm b) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_linearForm]
  simp

/-- The partial derivative of a formal linear form is its corresponding
constant coefficient. -/
@[simp] theorem pderiv_linearForm {σ R : Type*} [CommSemiring R]
    (b : σ → R) (i : σ) : pderiv i (linearForm b) = C (b i) := by
  classical
  ext d
  rw [coeff_pderiv, coeff_linearForm, map_add, Finsupp.degree_single, coeff_C]
  by_cases h : d = 0
  · subst d
    simp
  · have hd : d.degree ≠ 0 := fun h0 => h ((Finsupp.degree_eq_zero_iff d).1 h0)
    rw [ite_eq_right (by omega), ite_eq_right h, zero_mul]

/-- Mapping the coefficient ring commutes with forming a formal linear form. -/
theorem map_linearForm {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (b : σ → R) :
    map f (linearForm b) = linearForm (fun i => f (b i)) := by
  ext d
  rw [coeff_map, coeff_linearForm, coeff_linearForm]
  by_cases h : d.degree = 1
  · simp only [ite_eq_left h, map_sum]
  · simp only [ite_eq_right h, map_zero]

end MvPowerSeries
