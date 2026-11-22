/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

@[expose] public section

open Finset Matrix MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

namespace MathlibExtTest.Probability.Statistics.LassoRestrictedEigenvalue

/-- Non-vacuity of the restricted eigenvalue condition: the `n × n` identity design satisfies it
with `κ = 1 / n` over every cone. -/
lemma restrictedEigenvalue_one {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (α : ℝ) :
    RestrictedEigenvalue (1 : Matrix (Fin n) (Fin n) ℝ) S (1 / n) α :=
  ⟨by positivity, fun Δ _ => by simp⟩

/-- Every vector supported on `S` lies in every cone `C(S; α)` with `α ≥ 0`. -/
example {n : ℕ} (S : Finset (Fin n)) (Δ : Fin n → ℝ) (hΔ : ∀ j ∉ S, Δ j = 0) {α : ℝ}
    (hα : 0 ≤ α) : Δ ∈ cone S α := by
  have : ∑ j ∈ Sᶜ, |Δ j| = 0 :=
    sum_eq_zero fun j hj => by simp [hΔ j (mem_compl.mp hj)]
  show ∑ j ∈ Sᶜ, |Δ j| ≤ α * ∑ j ∈ S, |Δ j|
  rw [this]
  exact mul_nonneg hα (sum_nonneg fun _ _ => abs_nonneg _)

/-- The Lagrangian Lasso bound instantiated on the identity design (orthogonal design): any
minimiser is within `3 n √s lam` of `θ*`. -/
example {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (θs θhat : Fin n → ℝ) (w : Fin n → ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hsupp : ∀ j ∉ S, θs j = 0)
    (hnoise : ∀ j, |((1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hmin : ∀ θ, lassoObjective (1 : Matrix (Fin n) (Fin n) ℝ)
        ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ θs + w) lam θhat ≤
      lassoObjective (1 : Matrix (Fin n) (Fin n) ℝ)
        ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ θs + w) lam θ) :
    Real.sqrt (∑ j, (θhat j - θs j) ^ 2) ≤ 3 / (1 / n) * Real.sqrt S.card * lam :=
  lasso_l2_error_le (1 : Matrix (Fin n) (Fin n) ℝ) S θs θhat w hlam hsupp
    (restrictedEigenvalue_one hn S 3) hnoise hmin

/-- Zero noise and `θ̂ = θ*` satisfy the hypotheses of the basic inequality. -/
example {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) (θs : Fin n → ℝ)
    (hsupp : ∀ j ∉ S, θs j = 0) :
    θs - θs ∈ cone S 3 :=
  (lasso_basic_inequality X S θs θs 0 one_pos hsupp (by simp) le_rfl).1

/-- The slow rate needs no restricted eigenvalue condition: with `θ* = 0` the bound forces the
fitted values of any minimiser to vanish. -/
example {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (θhat : Fin d → ℝ) (w : Fin n → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hmin : ∀ θ, lassoObjective X (X *ᵥ 0 + w) lam θhat ≤ lassoObjective X (X *ᵥ 0 + w) lam θ) :
    (1 / n) * ∑ i, (X *ᵥ (θhat - 0)) i ^ 2 ≤ 12 * 0 * lam :=
  lasso_prediction_error_le_slow X 0 θhat w hlam hnoise (by simp) hmin

/-- The fast rate on the identity design, where `κ = 1 / n`. -/
example {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (θs θhat : Fin n → ℝ) (w : Fin n → ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hsupp : ∀ j ∉ S, θs j = 0)
    (hnoise : ∀ j, |((1 : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hmin : ∀ θ, lassoObjective (1 : Matrix (Fin n) (Fin n) ℝ)
        ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ θs + w) lam θhat ≤
      lassoObjective (1 : Matrix (Fin n) (Fin n) ℝ)
        ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ θs + w) lam θ) :
    (1 / n) * ∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (θhat - θs)) i ^ 2 ≤
      9 / (1 / n) * S.card * lam ^ 2 :=
  lasso_prediction_error_le_fast (1 : Matrix (Fin n) (Fin n) ℝ) S θs θhat w hlam hsupp
    (restrictedEigenvalue_one hn S 3) hnoise hmin

end MathlibExtTest.Probability.Statistics.LassoRestrictedEigenvalue
