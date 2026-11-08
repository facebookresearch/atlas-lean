/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Sequence.KalmanFilter

open Cslib.MachineLearning.Sequence.KalmanFilter MeasureTheory ProbabilityTheory Matrix WithLp

-- Scalar random walk `x' = x + w`, `w ~ N(0, 1)`, from `N(0, 1)`: the predicted variance is 2.
example : (predict (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ⟨0, 1⟩).cov = 2 := by
  simp [predict]
  norm_num

-- Observing it directly with noise variance 2 gives the gain `2 / (2 + 2) = 1 / 2`.
example : gain (1 : Matrix (Fin 1) (Fin 1) ℝ) !![2] ⟨0, !![2]⟩ 0 0 = 1 / 2 := by
  simp [gain, mul_apply]
  norm_num

-- One exact filter step for a two-dimensional state observed through one coordinate.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {x w : Ω → EuclideanSpace ℝ (Fin 2)} {v : Ω → EuclideanSpace ℝ (Fin 1)}
    (hx : Measurable x) (hw : Measurable w) (hv : Measurable v) (hxw : IndepFun x w P)
    (hxwv : IndepFun (fun ω => (x ω, w ω)) v P) {b : Belief (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : Matrix (Fin 1) (Fin 1) ℝ} (hP : b.cov.PosSemidef)
    (hQ : Q.PosSemidef) (hR : R.PosSemidef) (hxl : P.map x = b.law)
    (hwl : P.map w = multivariateGaussian 0 Q) (hvl : P.map v = multivariateGaussian 0 R)
    (F : Matrix (Fin 2) (Fin 2) ℝ) (H : Matrix (Fin 1) (Fin 2) ℝ)
    (hinv : IsUnit (H * (predict F Q b).cov * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω),
      condDistrib (fun ω => toEuclideanLin F (x ω) + w ω)
          (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω) P y =
        (step F Q H R y b).law :=
  condDistrib_step hx hw hv hxw hxwv hP hQ hR hxl hwl hvl F H hinv

-- Filter steps keep the belief a valid Gaussian.
example (F Q : Matrix (Fin 2) (Fin 2) ℝ) (H : Matrix (Fin 1) (Fin 2) ℝ)
    {R : Matrix (Fin 1) (Fin 1) ℝ} (y : EuclideanSpace ℝ (Fin 1)) {b : Belief (Fin 2)}
    (hb : b.Valid) (hQ : Q.PosSemidef) (hR : R.PosDef) : (step F Q H R y b).Valid :=
  step_valid F Q H y hb hQ hR

#print axioms condDistrib_step
