/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modifications copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
Licensed under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Normed.Lp.Finsupp

/-!
# Rational coefficient L1 bounds for multivariate polynomials

`MvPolynomial.coeffL1Norm` is the rational sum of absolute coefficients.
It is subadditive and submultiplicative. Its real cast is the distance to zero
in the explicit `WithLp 1` metric on the coefficient Finsupp, not the ordinary
Finsupp supremum norm. No polynomial norm instance is installed.

Adapted from `GeneralPieces.Sizes.l1` and its bounds in
`anthropics/formal-math`, `proof/rates/GeneralPieces/Ring/Sizes.lean`, lines
220–259, at commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
The original `AppHalfPieces.V` is `MvPolynomial ℕ+ ℚ`; the variable type here
is arbitrary, while the coefficient domain remains exactly rational.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {σ : Type*}

/-- The rational sum of the absolute values of a polynomial's coefficients. -/
noncomputable def coeffL1Norm (p : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ p.support, |p.coeff m|

/-- Enlarging the summation set beyond the support does not change the sum. -/
theorem coeffL1Norm_eq_sum {p : MvPolynomial σ ℚ} {S : Finset (σ →₀ ℕ)}
    (hS : p.support ⊆ S) : coeffL1Norm p = ∑ m ∈ S, |p.coeff m| :=
  sum_subset hS fun m _ hm ↦ by rw [notMem_support_iff.1 hm, abs_zero]

/-- The coefficient L1 norm is nonnegative. -/
theorem coeffL1Norm_nonneg (p : MvPolynomial σ ℚ) : 0 ≤ coeffL1Norm p :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The zero polynomial has coefficient L1 norm zero. -/
@[simp]
theorem coeffL1Norm_zero : coeffL1Norm (0 : MvPolynomial σ ℚ) = 0 := by
  simp [coeffL1Norm]

/-- Adding polynomials increases the coefficient L1 norm by at most the sum. -/
theorem coeffL1Norm_add_le (p q : MvPolynomial σ ℚ) :
    coeffL1Norm (p + q) ≤ coeffL1Norm p + coeffL1Norm q := by
  classical
  rw [coeffL1Norm_eq_sum (support_add (p := p) (q := q)),
    coeffL1Norm_eq_sum (p := p) (subset_union_left (s₂ := q.support)),
    coeffL1Norm_eq_sum (p := q) (subset_union_right (s₁ := p.support)),
    ← sum_add_distrib]
  exact sum_le_sum fun m _ ↦ by
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact abs_add_le _ _

/-- The norm of a finite sum is bounded by the sum of the coefficient norms. -/
theorem coeffL1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℚ) :
    coeffL1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (coeffL1Norm_add_le (f i) (∑ j ∈ s, f j)).trans
      (add_le_add le_rfl ih)

/-- Rational scalar multiplication scales the norm by the scalar's absolute value. -/
@[simp]
theorem coeffL1Norm_smul (a : ℚ) (p : MvPolynomial σ ℚ) :
    coeffL1Norm (a • p) = |a| * coeffL1Norm p := by
  rw [coeffL1Norm_eq_sum (support_smul (a := a) (f := p)), coeffL1Norm, mul_sum]
  exact sum_congr rfl fun m _ ↦ by rw [MvPolynomial.coeff_smul, smul_eq_mul, abs_mul]

/-- A monomial's coefficient L1 norm is the absolute value of its coefficient,
including when the coefficient is zero. -/
@[simp]
theorem coeffL1Norm_monomial (m : σ →₀ ℕ) (a : ℚ) :
    coeffL1Norm (monomial m a) = |a| := by
  classical
  rw [coeffL1Norm_eq_sum (support_monomial_subset (s := m) (a := a)), sum_singleton]
  simp only [MvPolynomial.coeff_monomial, ite_true]

/-- The coefficient L1 norm of a monomial is at most its absolute coefficient. -/
theorem coeffL1Norm_monomial_le (m : σ →₀ ℕ) (a : ℚ) :
    coeffL1Norm (monomial m a) ≤ |a| :=
  (coeffL1Norm_monomial m a).le

/-- The coefficient convolution in a product is bounded by the product of the
coefficient L1 norms; cancellation can make this inequality strict. -/
theorem coeffL1Norm_mul_le (p q : MvPolynomial σ ℚ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q := by
  classical
  have he : p * q = ∑ m ∈ p.support, ∑ n ∈ q.support,
      monomial (m + n) (p.coeff m * q.coeff n) := by
    conv_lhs => rw [← support_sum_monomial_coeff p, ← support_sum_monomial_coeff q]
    rw [sum_mul_sum]
    simp_rw [monomial_mul_monomial]
  calc
    coeffL1Norm (p * q) ≤ ∑ m ∈ p.support, ∑ n ∈ q.support,
        |p.coeff m| * |q.coeff n| := by
      rw [he]
      apply (coeffL1Norm_sum_le _ _).trans
      apply sum_le_sum
      intro m _
      apply (coeffL1Norm_sum_le _ _).trans
      exact sum_le_sum fun n _ ↦ (coeffL1Norm_monomial_le _ _).trans_eq (abs_mul _ _)
    _ = coeffL1Norm p * coeffL1Norm q := by rw [coeffL1Norm, coeffL1Norm, sum_mul_sum]

-- The metric needs the tautological exponent side condition, not a new hypothesis.
local instance : Fact ((1 : NNReal) ≤ 1) := ⟨le_rfl⟩

/-- The real cast of the coefficient L1 norm agrees with the explicit exponent-one
metric on the exact rational coefficient Finsupp carrier. -/
theorem dist_coeff_zero_eq_coeffL1Norm (p : MvPolynomial σ ℚ) :
    dist (WithLp.toLp ((1 : NNReal) : ENNReal) p.coeff)
      (WithLp.toLp ((1 : NNReal) : ENNReal) (0 : (σ →₀ ℕ) →₀ ℚ)) =
        (coeffL1Norm p : ℝ) := by
  rw [Finsupp.dist_def]
  simp only [NNReal.coe_one, inv_one, Real.rpow_one]
  have hz : p.coeff.zipWith dist (dist_self (0 : ℚ)) 0 =
      p.coeff.mapRange (fun a : ℚ ↦ |(a : ℝ)|) (by simp) := by
    ext m
    change dist (p.coeff m) (0 : ℚ) = |(p.coeff m : ℝ)|
    simp only [Rat.dist_eq, Rat.cast_zero, sub_zero]
  rw [hz, Finsupp.sum_mapRange_index (fun _ ↦ rfl)]
  simp only [Finsupp.sum, coeffL1Norm, Rat.cast_sum, Rat.cast_abs]
  rfl

end MvPolynomial
