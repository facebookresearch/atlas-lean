/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GaussianProcessMarginalLikelihood

open Cslib.MachineLearning.GaussianProcessRegression MeasureTheory ProbabilityTheory Matrix
  MetaMathlibExt

-- The zero kernel: the targets are pure noise and the evidence is that of N(0, σ² I).
example : kernelMatrix (fun _ _ => (0 : ℝ)) (id : Fin 2 → Fin 2) id = 0 := by
  ext i j; simp [kernelMatrix]

-- Non-vacuity: the log-evidence formula for two training points under the zero kernel.
example (y : EuclideanSpace ℝ (Fin 2)) :
    Real.log (multivariateGaussianPDFReal 0
        (kernelMatrix (fun _ _ => (0 : ℝ)) (id : Fin 2 → Fin 2) id + (1 : ℝ) • 1) y) =
      logMarginalLikelihood (fun _ _ => (0 : ℝ)) 1 (id : Fin 2 → Fin 2) y := by
  refine log_marginalLikelihood _ _ one_pos ?_ y
  have h : kernelMatrix (fun _ _ => (0 : ℝ)) (id : Fin 2 → Fin 2) id = 0 := by
    ext i j; simp [kernelMatrix]
  rw [h]
  exact PosSemidef.zero

-- The closed form at the origin with unit noise: only the normalisation term survives.
example : logMarginalLikelihood (fun _ _ => (0 : ℝ)) 1 (id : Fin 2 → Fin 2) 0 =
    -Real.log (2 * Real.pi) := by
  have h : kernelMatrix (fun _ _ => (0 : ℝ)) (id : Fin 2 → Fin 2) id = 0 := by
    ext i j; simp [kernelMatrix]
  simp [logMarginalLikelihood, h]

-- The marginal law of the targets for a kernel with positive semidefinite Gram matrix.
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (k : ℝ → ℝ → ℝ) (xs : Fin 3 → ℝ) (hK : (kernelMatrix k xs xs).PosSemidef)
    {f ε : Ω → EuclideanSpace ℝ (Fin 3)} (hf : Measurable f) (hε : Measurable ε)
    (hind : IndepFun f ε P) (hfl : P.map f = multivariateGaussian 0 (kernelMatrix k xs xs))
    (hεl : P.map ε = multivariateGaussian 0 ((2 : ℝ) • 1)) :
    P.map (fun ω => f ω + ε ω) = multivariateGaussian 0 (kernelMatrix k xs xs + (2 : ℝ) • 1) :=
  map_targets_eq k xs (by norm_num) hK hf hε hind hfl hεl
