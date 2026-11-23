/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.LeastSquares

/-!
# OLS residuals sum to zero with an intercept

A design `X : Matrix (Fin m) ι ℝ` has an intercept column `j` when every row has a `1` in
column `j`. The `j`-th normal equation is then the statement that the residuals
`y - X θ` sum to zero.

## Main results

* `Cslib.MachineLearning.LeastSquares.sum_residual_eq_zero_of_normal`: at any solution of
  the normal equations (no rank condition) the residuals sum to zero (`normal_iff`).
* `Cslib.MachineLearning.LeastSquares.sum_residual_eq_zero_of_rss_le`: the same at any
  residual-sum-of-squares minimizer (`rss_le_iff_normal`).

The simple-regression case is `MathlibExt.Probability.FiniteProbability.sum_resid_ols`.
Without an intercept the residuals need not sum to zero (see the tests).

## References

MIT 14.32 Econometrics; Wooldridge, *Introductory Econometrics*, OLS algebraic properties.
Atlas roadmap target ST01.T01.
-/

@[expose] public section

namespace Cslib.MachineLearning.LeastSquares

open Matrix Finset

/-- An intercept column: every row of the design `X` has a `1` in column `j`
(source clause: "the regression includes an intercept"). -/
def HasInterceptColumn {ι : Type*} {m : ℕ} (X : Matrix (Fin m) ι ℝ) (j : ι) : Prop :=
  ∀ k, X k j = 1

/-- At any solution `θ` of the normal equations `Xᵀ X θ = Xᵀ y` of a design with an
intercept column, the residuals `y - X θ` sum to zero. No rank condition is needed. -/
theorem sum_residual_eq_zero_of_normal {ι : Type*} [Fintype ι] {m : ℕ}
    {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {θ : ι → ℝ} {j : ι}
    (hθ : Xᵀ *ᵥ (X *ᵥ θ) = Xᵀ *ᵥ y) (hj : HasInterceptColumn X j) :
    ∑ k, (y - X *ᵥ θ) k = 0 := by
  have h0 : Xᵀ *ᵥ (y - X *ᵥ θ) = 0 := (normal_iff X y θ).1 hθ
  have h := congrFun h0 j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at h
  have hj' : ∀ k, X k j = 1 := hj
  simp only [hj', one_mul] at h
  exact h

/-- With an intercept, OLS residuals sum to zero: if `θ` minimizes the residual sum of
squares of a design with an intercept column, the residuals sum to zero
(Atlas roadmap ST01.T01). -/
theorem sum_residual_eq_zero_of_rss_le {ι : Type*} [Fintype ι] {m : ℕ}
    {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {θ : ι → ℝ} {j : ι}
    (hmin : ∀ θ', rss X y θ ≤ rss X y θ') (hj : HasInterceptColumn X j) :
    ∑ k, (y - X *ᵥ θ) k = 0 := by
  exact sum_residual_eq_zero_of_normal ((rss_le_iff_normal X y θ).1 hmin) hj

end Cslib.MachineLearning.LeastSquares
