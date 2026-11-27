/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Generative.GaussianDiscriminant

/-!
# Tests for Gaussian discriminant analysis

* Quadratic forms (Mathlib's `Matrix.toQuadraticForm'`): with `S = 2 I` on `Fin 2`, the value at
  `![1, 1]` is `4`.
* The one-dimensional density is Mathlib's.
* With unit precision on `Fin 2`, `gaussianDensity` is the density of Mathlib's
  `multivariateGaussian 0 1`.
* A one-dimensional model with uniform prior, means `1` and `-1` and unit precision: the
  posterior of `true` at `x` is `sigmoid (2 x)`.
* Four labelled points `0, 2` (class `true`) and `1, 3` (class `false`): the class means are `1`
  and `2`, the maximum likelihood covariance `mleCov` is `1` (positive definite), and the joint
  maximum likelihood statement is instantiated on this data.
-/

@[expose] public section

namespace Cslib.MachineLearning.GaussianDiscriminantTests

open Cslib.MachineLearning GaussianDiscriminant Matrix Categorical Convexity

example : (2 : Matrix (Fin 2) (Fin 2) ℝ).toQuadraticForm' ![1, 1] = 4 := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct, mulVec, Fin.sum_univ_two,
    ofNat_apply]
  norm_num

example (μ x : ℝ) : gaussianDensity (Matrix.of fun _ _ : Unit => (1 : ℝ)⁻¹) (fun _ => μ)
    (fun _ => x) = ProbabilityTheory.gaussianPDFReal μ 1 x := by
  simpa using gaussianDensity_unit μ x one_ne_zero

/-- The uniform distribution on `Bool`. -/
noncomputable def half : StdSimplex ℝ Bool :=
  StdSimplex.ofWeights (fun _ => 1 / 2) (fun _ => by norm_num) (by simp)

/-- Uniform prior, means `1` and `-1`, unit precision. -/
noncomputable def q : Params Bool Unit where
  prior := half
  mean c _ := if c then 1 else -1
  prec := 1

example (x : Unit → ℝ) : q.posterior x true = Real.sigmoid (2 * x ()) := by
  rw [Params.posterior_true_eq_sigmoid (by simpa [q] using PosDef.one)
    (fun c => by simp [q, half])]
  have h : (q.prec *ᵥ (q.mean true - q.mean false)) ⬝ᵥ x + (Real.log (q.prior.weights true /
      q.prior.weights false) - (q.prec.toQuadraticForm' (q.mean true) -
        q.prec.toQuadraticForm' (q.mean false)) / 2) = 2 * x () := by
    norm_num [q, half, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct, mulVec]
  rw [h]

example : ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (0 : Fin 2 → ℝ)) 1 =
    MeasureTheory.volume.withDensity
      fun x =>
        ENNReal.ofReal (gaussianDensity (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 (WithLp.ofLp x)) := by
  rw [← multivariateGaussian_eq_withDensity_gaussianDensity PosDef.one, inv_one]

/-- Labels of four points. -/
def y4 : Fin 4 → Bool := ![true, true, false, false]

/-- The points `0, 2, 1, 3`. -/
def x4 : Fin 4 → Unit → ℝ := ![fun _ => 0, fun _ => 2, fun _ => 1, fun _ => 3]

theorem members_true : Params.members y4 true = {0, 1} := by decide

theorem members_false : Params.members y4 false = {2, 3} := by decide

theorem mleMean_true : Params.mleMean y4 x4 true = fun _ => 1 := by
  funext u
  simp [Params.mleMean, Finset.centerMass, members_true, x4]

theorem mleMean_false : Params.mleMean y4 x4 false = fun _ => 2 := by
  funext u
  simp [Params.mleMean, Finset.centerMass, members_false, x4]
  norm_num

theorem mleCov_eq : Params.mleCov y4 x4 = 1 := by
  ext u v
  simp only [Params.mleCov, Params.scatter_eq, Fin.sum_univ_four,
    show y4 0 = true from rfl, show y4 1 = true from rfl, show y4 2 = false from rfl,
    show y4 3 = false from rfl, mleMean_true, mleMean_false]
  simp [x4, vecMulVec]
  norm_num

/-- The pooled scatter matrix is symmetric (MathlibExt's `weightedScatter_transpose`). -/
example :
    (Params.scatter y4 x4 (Params.mleMean y4 x4))ᵀ = Params.scatter y4 x4 (Params.mleMean y4 x4) :=
  Params.scatter_transpose y4 x4 _

example (p : Params Bool Unit) (hS : p.prec.PosDef) :
    Params.likelihood y4 x4 p ≤
      Params.likelihood y4 x4 (Params.mle y4 x4 (Params.mleCov y4 x4)⁻¹) :=
  Params.likelihood_le_mle_mleCov y4 x4 hS (by rw [mleCov_eq]; exact PosDef.one)

end Cslib.MachineLearning.GaussianDiscriminantTests
