/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian expectation of a quadratic form

The calculation uses only the means and second moments of the coordinates. Neither the
quadratic-form matrix nor its product with the covariance needs to be symmetric. Positive
semidefiniteness is sufficient for the Gaussian covariance, including a degenerate law.
-/

@[expose] public section

namespace ProbabilityTheory

open Matrix MeasureTheory WithLp

variable {n : Type*} [Fintype n] [DecidableEq n] (m : EuclideanSpace ℝ n)
  {V : Matrix n n ℝ} (hV : V.PosSemidef) (K : Matrix n n ℝ)

include hV in
/-- For a Gaussian vector of mean `m` and covariance `V`, the quadratic form `xᵀ K x`
is integrable and has expectation `tr(K V) + mᵀ K m`, for any real matrix `K`. -/
theorem integral_quadratic_multivariateGaussian :
    let μ := multivariateGaussian m V
    Integrable (fun x : EuclideanSpace ℝ n => ofLp x ⬝ᵥ K *ᵥ ofLp x) μ ∧
      ∫ x, ofLp x ⬝ᵥ K *ᵥ ofLp x ∂μ = (K * V).trace + ofLp m ⬝ᵥ K *ᵥ ofLp m := by
  let μ := multivariateGaussian m V
  have hL (i : n) : MemLp (fun x : EuclideanSpace ℝ n => x i) 2 μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := n) i).comp_memLp' (IsGaussian.memLp_two_id (μ := μ))
  have hm (i : n) : ∫ x : EuclideanSpace ℝ n, x i ∂μ = m i := by
    rw [← EuclideanSpace.coe_proj,
      ContinuousLinearMap.integral_comp_id_comm (by exact IsGaussian.integrable_id),
      show (∫ x, x ∂μ) = m from integral_id_multivariateGaussian]
    rfl
  have hc (i j : n) : ∫ x : EuclideanSpace ℝ n, x i * x j ∂μ = V j i + m i * m j := by
    have hh := covariance_eval_multivariateGaussian (μ := m) hV i j
    rw [covariance_eq_sub (hL i) (hL j), hm, hm] at hh
    have he : V j i = V i j := by simpa using congrFun (congrFun hV.isHermitian.eq i) j
    simp only [Pi.mul_apply] at hh
    rw [he]; linarith
  have hint (i j : n) : Integrable (fun x : EuclideanSpace ℝ n => K i j * (x i * x j)) μ :=
    ((hL i).integrable_mul (hL j)).const_mul _
  have expand (x : EuclideanSpace ℝ n) : ofLp x ⬝ᵥ K *ᵥ ofLp x =
      ∑ i, ∑ j, K i j * (x i * x j) := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_left_comm]
  simp_rw [expand]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, integral_const_mul, hc, mul_add,
    Finset.sum_add_distrib]
  rfl

end ProbabilityTheory
