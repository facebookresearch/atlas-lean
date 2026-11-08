/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Weighted means and scatter matrices

For points `xᵢ` in `EuclideanSpace ℝ n` with real weights `wᵢ` (counts, responsibilities, or all
ones):

* `weightedMean`, `weightedScatter`: the weighted mean and the weighted scatter matrix about any
  point; at the weighted mean the latter is the weighted sample covariance.
* `sum_smul_sub_weightedMean`: the weighted residuals sum to zero.
* `sum_mul_quad_sub_eq`: **the bias-variance split** of a weighted quadratic form,
  `∑ w (x - μ)ᵀ A (x - μ) = ∑ w (x - m)ᵀ A (x - m) + (∑ w) (m - μ)ᵀ A (m - μ)` for symmetric `A`.
* `sum_mul_quad_eq_trace`: a weighted quadratic form is `(∑ w) tr (A C)` with `C` the scatter.
* `dotProduct_weightedScatter_mulVec`, `weightedScatter_transpose`, `weightedScatter_posDef`:
  **with positive weights and points not all in an affine hyperplane, the scatter matrix is
  positive definite**.

These are the facts behind closed-form Gaussian maximum likelihood estimates (sample mean and
sample covariance), used for full-covariance mixtures and probabilistic PCA in
`CSLibExt/MachineLearning/LatentVariable/`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open Matrix WithLp
open scoped RealInnerProductSpace

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- The weighted mean `(∑ i, w i xᵢ) / ∑ i, w i`. -/
noncomputable def weightedMean (w : ι → ℝ) (xs : ι → EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  (∑ i, w i)⁻¹ • ∑ i, w i • xs i

/-- The weighted scatter matrix about `μ`, `(∑ i, w i (xᵢ - μ)(xᵢ - μ)ᵀ) / ∑ i, w i`. At the
weighted mean it is the weighted sample covariance. -/
noncomputable def weightedScatter (w : ι → ℝ) (xs : ι → EuclideanSpace ℝ n)
    (μ : EuclideanSpace ℝ n) : Matrix n n ℝ :=
  (∑ i, w i)⁻¹ • ∑ i, w i • vecMulVec (ofLp (xs i - μ)) (ofLp (xs i - μ))

omit [Fintype n] in
/-- The weighted residuals about the weighted mean sum to zero. -/
theorem sum_smul_sub_weightedMean {w : ι → ℝ} (hw : ∑ i, w i ≠ 0)
    (xs : ι → EuclideanSpace ℝ n) : ∑ i, w i • (xs i - weightedMean w xs) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [weightedMean, smul_smul, mul_inv_cancel₀ hw, one_smul, sub_self]

/-- **The bias-variance split of a weighted quadratic form**: for symmetric `A`,
`∑ w (x - μ)ᵀ A (x - μ) = ∑ w (x - m)ᵀ A (x - m) + (∑ w) (m - μ)ᵀ A (m - μ)` with `m` the
weighted mean. -/
theorem sum_mul_quad_sub_eq {w : ι → ℝ} (hw : ∑ i, w i ≠ 0) (xs : ι → EuclideanSpace ℝ n)
    {A : Matrix n n ℝ} (hA : Aᵀ = A) (μ : EuclideanSpace ℝ n) :
    ∑ i, w i * (ofLp (xs i - μ) ⬝ᵥ A *ᵥ ofLp (xs i - μ)) =
      ∑ i, w i * (ofLp (xs i - weightedMean w xs) ⬝ᵥ A *ᵥ ofLp (xs i - weightedMean w xs)) +
        (∑ i, w i) * (ofLp (weightedMean w xs - μ) ⬝ᵥ A *ᵥ ofLp (weightedMean w xs - μ)) := by
  set m := weightedMean w xs
  set b := ofLp (m - μ)
  have hsplit : ∀ i, ofLp (xs i - μ) = ofLp (xs i - m) + b := fun i => by
    simp [b, ofLp_sub]
  have hsym : ∀ a : n → ℝ, b ⬝ᵥ A *ᵥ a = a ⬝ᵥ A *ᵥ b := fun a => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hcross : ∑ i, w i * (ofLp (xs i - m) ⬝ᵥ A *ᵥ b) = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ n => ofLp v ⬝ᵥ A *ᵥ b)
      (sum_smul_sub_weightedMean hw xs)
    simpa [ofLp_sum, sum_dotProduct, smul_dotProduct] using h
  simp only [hsplit, add_dotProduct, mulVec_add, dotProduct_add, hsym]
  have : ∀ i, w i * (ofLp (xs i - m) ⬝ᵥ A *ᵥ ofLp (xs i - m) +
      ofLp (xs i - m) ⬝ᵥ A *ᵥ b + (ofLp (xs i - m) ⬝ᵥ A *ᵥ b + b ⬝ᵥ A *ᵥ b)) =
      w i * (ofLp (xs i - m) ⬝ᵥ A *ᵥ ofLp (xs i - m)) +
        2 * (w i * (ofLp (xs i - m) ⬝ᵥ A *ᵥ b)) + w i * (b ⬝ᵥ A *ᵥ b) := fun i => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, ← Finset.sum_mul]
  ring

/-- A weighted quadratic form is a trace against the weighted scatter matrix:
`∑ w (x - μ)ᵀ A (x - μ) = (∑ w) tr (A C)`. -/
theorem sum_mul_quad_eq_trace {w : ι → ℝ} (hw : ∑ i, w i ≠ 0) (xs : ι → EuclideanSpace ℝ n)
    (A : Matrix n n ℝ) (μ : EuclideanSpace ℝ n) :
    ∑ i, w i * (ofLp (xs i - μ) ⬝ᵥ A *ᵥ ofLp (xs i - μ)) =
      (∑ i, w i) * (A * weightedScatter w xs μ).trace := by
  rw [weightedScatter, Matrix.mul_smul, trace_smul, Matrix.mul_sum, trace_sum, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, trace_smul, mul_vecMulVec, trace_vecMulVec, smul_eq_mul, dotProduct_comm]

/-- The quadratic form of a weighted scatter matrix:
`uᵀ C u = (∑ w (u ⬝ (x - μ))²) / ∑ w`. -/
theorem dotProduct_weightedScatter_mulVec (w : ι → ℝ) (xs : ι → EuclideanSpace ℝ n)
    (μ : EuclideanSpace ℝ n) (u : n → ℝ) :
    u ⬝ᵥ weightedScatter w xs μ *ᵥ u =
      (∑ i, w i)⁻¹ * ∑ i, w i * (u ⬝ᵥ ofLp (xs i - μ)) ^ 2 := by
  simp only [weightedScatter, smul_mulVec, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_comm (ofLp (xs i - μ)) u]
  ring

omit [Fintype n] in
theorem weightedScatter_transpose (w : ι → ℝ) (xs : ι → EuclideanSpace ℝ n)
    (μ : EuclideanSpace ℝ n) : (weightedScatter w xs μ)ᵀ = weightedScatter w xs μ := by
  simp [weightedScatter, transpose_smul, transpose_sum, transpose_vecMulVec]

/-- **Weighted scatter matrices of points in general position are positive definite**: with
positive weights, and points not all in an affine hyperplane (for every nonzero direction `v` the
projections `⟪v, xᵢ⟫` are not all equal). -/
theorem weightedScatter_posDef {w : ι → ℝ} (hw : ∀ i, 0 < w i) {xs : ι → EuclideanSpace ℝ n}
    (hspan : ∀ v : EuclideanSpace ℝ n, v ≠ 0 → ∃ i j, ⟪v, xs i⟫ ≠ ⟪v, xs j⟫)
    (μ : EuclideanSpace ℝ n) : (weightedScatter w xs μ).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, weightedScatter_transpose]
  · rw [star_trivial, dotProduct_weightedScatter_mulVec]
    obtain ⟨i, j, hij⟩ := hspan (toLp 2 u) (fun h => hu (by simpa using congrArg ofLp h))
    have hW : 0 < ∑ k, w k := Finset.sum_pos (fun k _ => hw k) ⟨i, Finset.mem_univ i⟩
    refine mul_pos (inv_pos.2 hW) ?_
    have hne : u ⬝ᵥ ofLp (xs i - μ) ≠ 0 ∨ u ⬝ᵥ ofLp (xs j - μ) ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      apply hij
      have h1 := hcon.1
      have h2 := hcon.2
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_sub,
        dotProduct_sub] at h1 h2 ⊢
      rw [dotProduct_comm, dotProduct_comm (ofLp (xs j))]
      linarith
    have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ w k * (u ⬝ᵥ ofLp (xs k - μ)) ^ 2 :=
      fun k _ => mul_nonneg (hw k).le (sq_nonneg _)
    rcases hne with h | h
    · exact lt_of_lt_of_le (mul_pos (hw i) (by positivity))
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    · exact lt_of_lt_of_le (mul_pos (hw j) (by positivity))
        (Finset.single_le_sum hnonneg (Finset.mem_univ j))

end MetaMathlibExt
