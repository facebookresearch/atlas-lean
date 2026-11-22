/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.HighDimensional.LassoBasicInequality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

/-!
# Tests for the fixed-design Lasso basic inequality

* Use: the noiseless case `ε = 0` and the soft-threshold estimate for `n = d = 1`.
* Degenerate `θhat = θstar` and boundary `τ ≤ 0`.
* Non-vacuity of the Lasso hypothesis for `d = 0`.
* Concrete `ℓ₁` and squared `ℓ₂` norms of `(1, -2)`.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.HighDimensional

/-- Use (noiseless, `ε = 0`): the prediction error is controlled by the `ℓ₁` gap alone. -/
example {n d : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin d) ℝ) (θstar θhat : Fin d → ℝ)
    (τ : ℝ) (hY : IsLassoEstimator X (X.mulVec θstar) τ θhat) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) ≤
      2 * τ * (l1norm θstar - l1norm θhat) := by
  have h := lasso_basic_inequality hn X θstar 0 τ θhat (by simpa using hY)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  linarith only [h]

/-- Degenerate (`θhat = θstar`): `lasso_basic_inequality` specialized at `θhat = θstar`; the
prediction term and the score term both vanish, so the comparison reduces to the equal-penalty
reflexivity `2τ ‖θstar‖₁ ≤ 2τ ‖θstar‖₁` (the registry `0 ≤ 0` vacuity check). -/
example {n d : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin d) ℝ) (θstar : Fin d → ℝ)
    (ε : Fin n → ℝ) (τ : ℝ) (hY : IsLassoEstimator X (X.mulVec θstar + ε) τ θstar) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θstar - θstar)) + 2 * τ * l1norm θstar ≤
      (2 / (n : ℝ)) * (∑ i, ε i * X.mulVec (θstar - θstar) i) + 2 * τ * l1norm θstar ∧
      (1 / (n : ℝ)) * sqL2norm (X.mulVec (θstar - θstar)) = 0 ∧
      (∑ i, ε i * X.mulVec (θstar - θstar) i) = 0 := by
  refine ⟨lasso_basic_inequality hn X θstar ε τ θstar hY, ?_, ?_⟩
  · simp [sub_self, Matrix.mulVec_zero, sqL2norm]
  · simp [sub_self, Matrix.mulVec_zero]

/-- Boundary: a nonpositive tuning parameter never yields a Lasso estimator. -/
example {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ)
    (hτ : τ ≤ 0) : ¬ IsLassoEstimator X Y τ θhat := by
  exact fun h => absurd h.1 (not_lt.2 hτ)

/-- Non-vacuity: with no covariates (`d = 0`) every `τ > 0` makes the unique vector a Lasso
estimator, so the hypothesis of the basic inequality is satisfiable. -/
example {n : ℕ} (X : Matrix (Fin n) (Fin 0) ℝ) (Y : Fin n → ℝ) (θhat : Fin 0 → ℝ) :
    IsLassoEstimator X Y 1 θhat := by
  refine ⟨one_pos, fun θ => ?_⟩
  have heq : θ = θhat := Subsingleton.elim θ θhat
  subst heq
  exact le_rfl

/-- Use (soft threshold): for `n = d = 1`, `X = 1`, `Y = 3`, `τ = 1` the Lasso estimate is the soft
threshold `3 - 1 = 2`. This fails if the penalty is `τ ‖θ‖₁` instead of `2τ ‖θ‖₁`. -/
example : IsLassoEstimator (fun _ _ => (1 : ℝ) : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ => (3 : ℝ)) 1 (fun _ => (2 : ℝ)) := by
  refine ⟨one_pos, fun θ => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, sqL2norm, l1norm,
    Pi.sub_apply, one_mul]
  norm_num
  rcases le_total 0 (θ 0) with ht | ht
  · rw [abs_of_nonneg ht]
    nlinarith [sq_nonneg (θ 0 - 2)]
  · rw [abs_of_nonpos ht]
    nlinarith [sq_nonneg (θ 0 - 2)]

/-- Compute: `‖(1, -2)‖₁ = 3`. -/
example : l1norm (![1, -2] : Fin 2 → ℝ) = 3 := by
  simp [l1norm, Fin.sum_univ_two]
  norm_num

/-- Compute: `‖(1, -2)‖₂² = 5`. -/
example : sqL2norm (![1, -2] : Fin 2 → ℝ) = 5 := by
  simp [sqL2norm, Fin.sum_univ_two]
  norm_num

end MathlibExt.Probability.Statistics.HighDimensional
