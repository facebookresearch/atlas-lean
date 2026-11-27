/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.LeastSquares
public import Mathlib.Analysis.InnerProductSpace.PiL2

import MathlibExt.Probability.Statistics.LinearModel.FittedProjection

/-!
# The set of least-squares minimizers

For any finite real design matrix, least-squares minimizers are a translate of its kernel,
and all yield the same fitted vector: the orthogonal projection onto the column space.
When the design is injective, the unique coefficient vector is given by the inverse Gram
formula. No rank or nonemptiness assumption is needed for the kernel or projection results.

See Boyd and Vandenberghe, *Introduction to Applied Linear Algebra* (2018), §12.2, for the
full-column-rank formula and orthogonality principle. We identify the residual sum of squares
with the squared Euclidean residual norm and reuse the rank-free fitted-projection theorem.
The normal equations provide the reference solution for the affine kernel description.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LeastSquares

open Matrix
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- The coefficient vectors minimizing the residual sum of squares over all coefficients. -/
def rssMinimizers (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) : Set (ι → ℝ) :=
  {θ | ∀ θ', rss X y θ ≤ rss X y θ'}

private theorem mem_rssMinimizers_iff_fit_eq_projection [DecidableEq ι]
    (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (θ : ι → ℝ) :
    θ ∈ rssMinimizers X y ↔
      WithLp.toLp 2 (X *ᵥ θ) =
        (LinearMap.range X.toEuclideanLin).starProjection (WithLp.toLp 2 y) := by
  let y₂ : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 y
  have hsq (γ : ι → ℝ) :
      rss X y γ = ‖y₂ - X.toEuclideanLin (WithLp.toLp 2 γ)‖ ^ 2 := by
    rw [rss_eq_sum, EuclideanSpace.real_norm_sq_eq]
    simp only [y₂, PiLp.sub_apply, Matrix.toLpLin_apply]
  have hcompare (γ : ι → ℝ) :
      rss X y θ ≤ rss X y γ ↔
        ‖y₂ - X.toEuclideanLin (WithLp.toLp 2 θ)‖ ≤
          ‖y₂ - X.toEuclideanLin (WithLp.toLp 2 γ)‖ := by
    rw [hsq θ, hsq γ, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hmin : θ ∈ rssMinimizers X y ↔ ∀ w : EuclideanSpace ℝ ι,
      ‖y₂ - X.toEuclideanLin (WithLp.toLp 2 θ)‖ ≤ ‖y₂ - X.toEuclideanLin w‖ := by
    constructor
    · intro h w
      simpa only [WithLp.toLp_ofLp] using (hcompare (WithLp.ofLp w)).mp (h (WithLp.ofLp w))
    · intro h γ
      exact (hcompare γ).mpr (h (WithLp.toLp 2 γ))
  exact hmin.trans
    ((MathlibExt.Probability.Statistics.LinearModel.least_squares_fitted_projection X y₂).1
      (WithLp.toLp 2 θ))

/-- Relative to a solution of the normal equations, a coefficient vector is minimizing exactly
when it gives the same fitted values. -/
theorem mem_rssMinimizers_iff_fit_eq {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ}
    {θ₀ : ι → ℝ} (h₀ : Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y) (θ : ι → ℝ) :
    θ ∈ rssMinimizers X y ↔ X *ᵥ θ = X *ᵥ θ₀ := by
  classical
  have hproj := (mem_rssMinimizers_iff_fit_eq_projection X y θ₀).mp (rss_le_of_normal h₀)
  rw [mem_rssMinimizers_iff_fit_eq_projection, ← hproj]
  constructor
  · exact congrArg (WithLp.ofLp (p := 2))
  · exact congrArg (WithLp.toLp 2)

/-- **The set of least-squares minimizers.** Starting from any solution of the normal equations,
translate the kernel of the design matrix by that solution to obtain all minimizers. -/
theorem rssMinimizers_eq_translate_ker {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ}
    {θ₀ : ι → ℝ} (h₀ : Xᵀ *ᵥ (X *ᵥ θ₀) = Xᵀ *ᵥ y) :
    rssMinimizers X y = (fun v => θ₀ + v) '' (↑(LinearMap.ker X.mulVecLin) : Set (ι → ℝ)) := by
  ext θ
  rw [mem_rssMinimizers_iff_fit_eq h₀]
  constructor
  · intro h
    refine ⟨θ - θ₀, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, h, sub_self]
    · change θ₀ + (θ - θ₀) = θ
      rw [add_sub_cancel]
  · rintro ⟨v, hv, rfl⟩
    change X *ᵥ v = 0 at hv
    rw [mulVec_add, hv, add_zero]

/-- **Uniqueness of least squares.** There is exactly one minimizing coefficient vector if and
only if multiplication by the design matrix is injective. -/
theorem existsUnique_rssMinimizer_iff_injective (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) :
    (∃! θ, θ ∈ rssMinimizers X y) ↔ Function.Injective X.mulVec := by
  constructor
  · rintro ⟨θ₀, hmin, huniq⟩ a b hab
    have h₀ := (rss_le_iff_normal X y θ₀).mp hmin
    have hfit : X *ᵥ (θ₀ + (a - b)) = X *ᵥ θ₀ := by
      rw [mulVec_add, mulVec_sub, hab, sub_self, add_zero]
    have he := huniq _ ((mem_rssMinimizers_iff_fit_eq h₀ _).mpr hfit)
    exact sub_eq_zero.mp (add_left_cancel (he.trans (add_zero θ₀).symm))
  · intro hinj
    obtain ⟨θ₀, h₀⟩ := exists_normal X y
    refine ⟨θ₀, (mem_rssMinimizers_iff_fit_eq h₀ θ₀).mpr rfl, ?_⟩
    exact fun θ hθ => hinj ((mem_rssMinimizers_iff_fit_eq h₀ θ).mp hθ)

/-- With an injective design, the inverse Gram formula gives the sole minimizer. -/
theorem rssMinimizers_eq_singleton_of_injective [DecidableEq ι]
    (X : Matrix (Fin m) ι ℝ) (y : Fin m → ℝ) (hX : Function.Injective X.mulVec) :
    rssMinimizers X y = {((Xᵀ * X)⁻¹ * Xᵀ) *ᵥ y} := by
  have hpos : (Xᵀ * X).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self X hX
  have hdet : IsUnit (Xᵀ * X).det := hpos.det_pos.ne'.isUnit
  ext θ
  rw [mem_rssMinimizers_iff_fit_eq (normal_inv hdet y), Set.mem_singleton_iff]
  exact ⟨fun h => hX h, fun h => congrArg X.mulVec h⟩

/-- **Unique fitted values are the orthogonal projection.** In Euclidean coordinates, every
least-squares minimizer fits the orthogonal projection of the response onto the column space.
This remains true for rank-deficient designs. -/
theorem fit_eq_starProjection_of_mem_rssMinimizers [DecidableEq ι]
    {X : Matrix (Fin m) ι ℝ} {y : Fin m → ℝ} {θ : ι → ℝ}
    (hθ : θ ∈ rssMinimizers X y) :
    WithLp.toLp 2 (X *ᵥ θ) =
      (LinearMap.range X.toEuclideanLin).starProjection (WithLp.toLp 2 y) :=
  (mem_rssMinimizers_iff_fit_eq_projection X y θ).mp hθ

end Cslib.MachineLearning.LeastSquares
