/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.Probability.FiniteProbability

/-!
# Finite covariance matrices are positive semidefinite

For a finite weight `p ≥ 0` and a random return vector `X : α → n → ℝ`, the portfolio variance of
weights `w` is the quadratic form of the covariance matrix, and the covariance matrix
`MathlibExt.Probability.FiniteProbability.covMatrix p X` is positive semidefinite.

## i. Overview

Bilinearity of the finite covariance (`covariance_sum_mul_sum`) identifies
`w ⬝ᵥ covMatrix p X *ᵥ w` with the variance of `x ↦ w ⬝ᵥ X x`, which is nonnegative for
nonnegative weights (`variance_nonneg`); symmetry is `transpose_covMatrix`. Only `0 ≤ p` is used,
not `∑ x, p x = 1`. Perfectly correlated returns give a singular covariance matrix, so positive
semidefinite cannot be strengthened to positive definite.

## ii. Main results

* `MathlibExt.Probability.FiniteProbability.dotProduct_covMatrix_mulVec`
* `MathlibExt.Probability.FiniteProbability.covMatrix_posSemidef`

## iii. References

* Z. Bodie, A. Kane, A. Marcus, *Investments*, ch. 7 (portfolio variance).
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.FiniteProbability

/-- **Portfolio variance.** For portfolio weights `w`, the quadratic form of the covariance
matrix is the variance of the portfolio return `x ↦ w ⬝ᵥ X x`, for every weight `p`. -/
theorem dotProduct_covMatrix_mulVec {α n : Type*} [Fintype α] [Fintype n] (p : α → ℝ)
    (X : α → n → ℝ) (w : n → ℝ) :
    w ⬝ᵥ (covMatrix p X *ᵥ w) = variance p (fun x => w ⬝ᵥ X x) := by
  have hdot : (fun x => w ⬝ᵥ X x) = (fun x => ∑ i ∈ Finset.univ, w i * X x i) := rfl
  rw [hdot, ← covariance_self, covariance_sum_mul_sum, Matrix.dot_mulVec_eq_sum_sum,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covMatrix_apply, covariance_comm]
  ring

/-- **The covariance matrix is positive semidefinite** under nonnegative weights. -/
theorem covMatrix_posSemidef {α n : Type*} [Fintype α] [Fintype n] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (X : α → n → ℝ) : (covMatrix p X).PosSemidef := by
  have hH : (covMatrix p X).IsHermitian := by
    show (covMatrix p X)ᴴ = covMatrix p X
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_covMatrix]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have hstar : star x = x := star_trivial x
  rw [hstar, dotProduct_covMatrix_mulVec]
  exact variance_nonneg hp0 _

end MathlibExt.Probability.FiniteProbability
