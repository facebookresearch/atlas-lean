/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GaussianProcessRegression

open Cslib.MachineLearning.GaussianProcessRegression MeasureTheory ProbabilityTheory Matrix

-- The squared-exponential kernel on the real line.
noncomputable def rbf (x x' : ℝ) : ℝ := Real.exp (-(x - x') ^ 2 / 2)

-- The kernel matrix is the kernel on the two input families.
example : kernelMatrix rbf (![0, 1] : Fin 2 → ℝ) (![2] : Fin 1 → ℝ) 1 0 = Real.exp (-1 / 2) := by
  simp only [kernelMatrix, rbf, of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  norm_num

-- The GP posterior for one test input and two noisy training targets.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (xt : Fin 1 → ℝ) (xs : Fin 2 → ℝ) {σ2 : ℝ} (hσ : 0 < σ2)
    {V : Ω → EuclideanSpace ℝ (Fin 1 ⊕ Fin 2)} (hV : Measurable V)
    (hk : (kernelMatrix rbf (Sum.elim xt xs) (Sum.elim xt xs)).PosSemidef)
    (hlaw : P.map V = multivariateGaussian 0 (jointCov rbf σ2 xt xs)) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (targetPart (τ := Fin 1)) (V ω)),
      condDistrib (fun ω => toEuclideanLin (testPart (ν := Fin 2)) (V ω))
          (fun ω => toEuclideanLin (targetPart (τ := Fin 1)) (V ω)) P y =
        multivariateGaussian
          (toEuclideanLin (kernelMatrix rbf xt xs * (kernelMatrix rbf xs xs + σ2 • 1)⁻¹) y)
          (kernelMatrix rbf xt xt -
            kernelMatrix rbf xt xs * (kernelMatrix rbf xs xs + σ2 • 1)⁻¹ *
              kernelMatrix rbf xs xt) :=
  condDistrib_test_given_targets rbf hσ xt xs hk hV hlaw

-- The joint covariance splits as kernel matrix plus training noise.
example (xt : Fin 1 → ℝ) (xs : Fin 2 → ℝ) :
    jointCov rbf 3 xt xs (Sum.inr 0) (Sum.inr 0) = rbf (xs 0) (xs 0) + 3 := by
  rw [jointCov_eq_add]
  simp [kernelMatrix]

#print axioms condDistrib_test_given_targets
