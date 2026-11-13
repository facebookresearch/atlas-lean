/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-design Lasso basic inequality

Rigollet's Definition 2.12 (`ℓ₁` norm, squared `ℓ₂` norm, Lasso estimator for a fixed design
`X : Matrix (Fin n) (Fin d) ℝ`) and the deterministic first steps of Rigollet Theorem 2.15: the
basic inequality
`(1/n) ‖X(θhat - θstar)‖² + 2τ ‖θhat‖₁ ≤ (2/n) ⟨ε, X(θhat - θstar)⟩ + 2τ ‖θstar‖₁`
for `Y = X θstar + ε`, and its transposed form with `⟨Xᵀ ε, θhat - θstar⟩`. Both hold pointwise
in `ε`; no noise law, score event, or restricted eigenvalue condition is assumed.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.HighDimensional

/-- `ℓ₁` norm of a coefficient vector: `∑ j, |θ j|`. -/
noncomputable def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, |θ j|

/-- Squared Euclidean norm of a vector: `∑ i, v i ^ 2`. -/
noncomputable def sqL2norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- **Lasso estimator** (Rigollet, Definition 2.12): `θhat` minimizes the penalized criterion
`(1/n) ‖Y - Xθ‖² + 2τ ‖θ‖₁` over all `θ`, with a positive tuning parameter `τ`. -/
def IsLassoEstimator {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  0 < τ ∧ ∀ θ : Fin d → ℝ,
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θhat) + 2 * τ * l1norm θhat ≤
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θ) + 2 * τ * l1norm θ

/-- Unfolding equation for `l1norm`. -/
theorem l1norm_eq_sum {d : ℕ} (θ : Fin d → ℝ) : l1norm θ = ∑ j, |θ j| := by
  rfl

/-- Unfolding equation for `sqL2norm`. -/
theorem sqL2norm_eq_sum {n : ℕ} (v : Fin n → ℝ) : sqL2norm v = ∑ i, v i ^ 2 := by
  rfl

/-- The `ℓ₁` norm is nonnegative. -/
theorem l1norm_nonneg {d : ℕ} (θ : Fin d → ℝ) : 0 ≤ l1norm θ := by
  exact Finset.sum_nonneg fun j _ => abs_nonneg _

/-- The squared `ℓ₂` norm is nonnegative. -/
theorem sqL2norm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqL2norm v := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- A Lasso estimator has a positive tuning parameter. -/
theorem IsLassoEstimator.tau_pos {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {Y : Fin n → ℝ}
    {τ : ℝ} {θhat : Fin d → ℝ} (h : IsLassoEstimator X Y τ θhat) : 0 < τ := by
  exact h.1

/-- **Lasso basic inequality** (deterministic first step of Rigollet Theorem 2.15). If `θhat` is a
Lasso estimator for the response `Y = X θstar + ε`, then
`(1/n) ‖X(θhat - θstar)‖² + 2τ ‖θhat‖₁ ≤ (2/n) ⟨ε, X(θhat - θstar)⟩ + 2τ ‖θstar‖₁`,
pointwise in `ε` (no noise law, no restricted eigenvalue condition). -/
theorem lasso_basic_inequality {n d : ℕ} (_hn : 0 < (n : ℝ))
    (X : Matrix (Fin n) (Fin d) ℝ) (θstar : Fin d → ℝ) (ε : Fin n → ℝ) (τ : ℝ)
    (θhat : Fin d → ℝ) (hY : IsLassoEstimator X (X.mulVec θstar + ε) τ θhat) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) + 2 * τ * l1norm θhat ≤
      (2 / (n : ℝ)) * (∑ i, ε i * X.mulVec (θhat - θstar) i) + 2 * τ * l1norm θstar := by
  have hres1 : (X.mulVec θstar + ε) - X.mulVec θhat = ε - X.mulVec (θhat - θstar) := by
    rw [Matrix.mulVec_sub]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hres2 : (X.mulVec θstar + ε) - X.mulVec θstar = ε := by
    rw [add_comm (X.mulVec θstar) ε, add_sub_cancel_right]
  have hexp : sqL2norm (ε - X.mulVec (θhat - θstar))
      = sqL2norm ε - 2 * (∑ i, ε i * X.mulVec (θhat - θstar) i)
        + sqL2norm (X.mulVec (θhat - θstar)) := by
    simp only [sqL2norm, Pi.sub_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 := hY.2 θstar
  rw [hres1, hres2, hexp] at h1
  have e1 : (1 / (n : ℝ)) * (sqL2norm ε - 2 * (∑ i, ε i * X.mulVec (θhat - θstar) i)
      + sqL2norm (X.mulVec (θhat - θstar)))
      = (1 / (n : ℝ)) * sqL2norm ε - (2 / (n : ℝ)) * (∑ i, ε i * X.mulVec (θhat - θstar) i)
        + (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) := by
    ring
  rw [e1] at h1
  linarith only [h1]

/-- **Lasso basic inequality, transposed form**:
`(1/n) ‖X(θhat - θstar)‖² ≤ (2/n) ⟨Xᵀ ε, θhat - θstar⟩ + 2τ (‖θstar‖₁ - ‖θhat‖₁)`. -/
theorem lasso_basic_inequality_transpose {n d : ℕ} (_hn : 0 < (n : ℝ))
    (X : Matrix (Fin n) (Fin d) ℝ) (θstar : Fin d → ℝ) (ε : Fin n → ℝ) (τ : ℝ)
    (θhat : Fin d → ℝ) (hY : IsLassoEstimator X (X.mulVec θstar + ε) τ θhat) :
    (1 / (n : ℝ)) * sqL2norm (X.mulVec (θhat - θstar)) ≤
      (2 / (n : ℝ)) * (∑ j, X.transpose.mulVec ε j * (θhat - θstar) j) +
        2 * τ * (l1norm θstar - l1norm θhat) := by
  have hswap : (∑ i, ε i * X.mulVec (θhat - θstar) i)
      = ∑ j, X.transpose.mulVec ε j * (θhat - θstar) j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hbase := lasso_basic_inequality _hn X θstar ε τ θhat hY
  rw [hswap] at hbase
  linarith only [hbase]

end MathlibExt.Probability.Statistics.HighDimensional
