/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith

/-!
# Kriging variance-difference certificate

For weights `u`, target variance `σ`, observation covariance
matrix `K`, and target covariance vector `c`, the ordinary
kriging prediction-error variance expression is `σ + u ⬝ᵥ (K *ᵥ
u) - 2 * (u ⬝ᵥ c)`. If `w` satisfies the constrained first-order
equation `K *ᵥ w + lam • 1 = c` and a competitor `v` also has
weights summing to one, the variance difference is exactly the
quadratic form `(v - w) ⬝ᵥ (K *ᵥ (v - w))`. Positive
semidefiniteness gives optimality and positive definiteness
gives uniqueness of the minimizer. This is the algebraic
certificate; no stochastic existence claim is made.

## Main results

- `MathlibExt.Probability.KrigingVariance.kriging_variance_difference`:
  the difference identity.
- `MathlibExt.Probability.KrigingVariance.krigingErrorVariance_le`:
  optimality under positive semidefinite `K`.
- `MathlibExt.Probability.KrigingVariance.kriging_weights_unique`:
  uniqueness under positive definite `K`.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.KrigingVariance

/-- Ordinary-kriging prediction-error variance expression for
weights `u`, target variance `σ`, observation covariance matrix
`K`, and target covariance vector `c`:
`σ + u ⬝ᵥ (K *ᵥ u) - 2 * (u ⬝ᵥ c)`. -/
noncomputable def krigingErrorVariance {n : Type*} [Fintype n]
    (σ : ℝ) (K : Matrix n n ℝ) (c u : n → ℝ) : ℝ :=
  σ + u ⬝ᵥ (K *ᵥ u) - 2 * (u ⬝ᵥ c)

/-- Variance-difference certificate: if `K` is symmetric, `w`
satisfies the constrained first-order equation
`K *ᵥ w + lam • 1 = c`, and both `w` and a competitor `v` have
weights summing to one, then
`variance(v) - variance(w) = (v - w) ⬝ᵥ (K *ᵥ (v - w))`. -/
theorem kriging_variance_difference {n : Type*} [Fintype n]
    {σ lam : ℝ} {K : Matrix n n ℝ} {c w v : n → ℝ}
    (hK : K.IsSymm) (hstat : K *ᵥ w + lam • (1 : n → ℝ) = c)
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1) :
    krigingErrorVariance σ K c v - krigingErrorVariance σ K c w
      = (v - w) ⬝ᵥ (K *ᵥ (v - w)) := by
  have hKt : Kᵀ = K := hK
  have hsym : ∀ a b : n → ℝ, a ⬝ᵥ (K *ᵥ b) = b ⬝ᵥ (K *ᵥ a) := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hKt, dotProduct_comm]
  have hcw : c - K *ᵥ w = lam • (1 : n → ℝ) := by
    rw [← hstat, add_sub_cancel_left]
  have hdot1 : (v - w) ⬝ᵥ (1 : n → ℝ) = 0 := by
    simp only [dotProduct, Pi.sub_apply, Pi.one_apply, mul_one,
      Finset.sum_sub_distrib, hv, hw, sub_self]
  have hlam : (v - w) ⬝ᵥ (lam • (1 : n → ℝ)) = 0 := by
    rw [dotProduct_smul, hdot1, smul_zero]
  have hstat0 : (v - w) ⬝ᵥ (K *ᵥ w) = (v - w) ⬝ᵥ c := by
    have h1 : (v - w) ⬝ᵥ (c - K *ᵥ w) = 0 := by
      rw [hcw]
      exact hlam
    rw [dotProduct_sub] at h1
    exact (sub_eq_zero.mp h1).symm
  have e1 : w ⬝ᵥ (K *ᵥ v) = v ⬝ᵥ (K *ᵥ w) := hsym w v
  simp only [krigingErrorVariance, mulVec_sub, dotProduct_sub,
    sub_dotProduct] at hstat0 ⊢
  linarith [e1, hstat0]

/-- Optimality from the certificate when `K` is positive
semidefinite. -/
theorem krigingErrorVariance_le {n : Type*} [Fintype n]
    {σ lam : ℝ} {K : Matrix n n ℝ} {c w v : n → ℝ}
    (hK : K.PosSemidef) (hstat : K *ᵥ w + lam • (1 : n → ℝ) = c)
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1) :
    krigingErrorVariance σ K c w
      ≤ krigingErrorVariance σ K c v := by
  have hsym : K.IsSymm := hK.1.isSymm
  have hdiff : krigingErrorVariance σ K c v - krigingErrorVariance σ K c w
      = (v - w) ⬝ᵥ (K *ᵥ (v - w)) :=
    kriging_variance_difference hsym hstat hw hv
  have hnonneg := hK.dotProduct_mulVec_nonneg (v - w)
  simp only [star_trivial] at hnonneg
  rw [← hdiff] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Uniqueness from the certificate when `K` is positive
definite: an equal-variance competitor has the same weights. -/
theorem kriging_weights_unique {n : Type*} [Fintype n]
    {σ lam : ℝ} {K : Matrix n n ℝ} {c w v : n → ℝ}
    (hK : K.PosDef) (hstat : K *ᵥ w + lam • (1 : n → ℝ) = c)
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1)
    (heq : krigingErrorVariance σ K c v
      = krigingErrorVariance σ K c w) :
    v = w := by
  have hsym : K.IsSymm := hK.1.isSymm
  have hdiff : krigingErrorVariance σ K c v - krigingErrorVariance σ K c w
      = (v - w) ⬝ᵥ (K *ᵥ (v - w)) :=
    kriging_variance_difference hsym hstat hw hv
  have h0 : (v - w) ⬝ᵥ (K *ᵥ (v - w)) = 0 := by
    rw [← hdiff, heq, sub_self]
  have hsub : v - w = 0 := by
    by_contra hne
    have hpos := hK.dotProduct_mulVec_pos hne
    simp only [star_trivial] at hpos
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  exact sub_eq_zero.mp hsub

end MathlibExt.Probability.KrigingVariance
