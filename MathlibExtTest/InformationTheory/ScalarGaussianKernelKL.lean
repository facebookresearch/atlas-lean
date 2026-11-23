/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ScalarGaussianKernelKL

@[expose] public section

open MathlibExt.InformationTheory.ScalarGaussianKernelKL
  MathlibExt.InformationTheory.VectorGaussianKernelKL
  MathlibExt.InformationTheory.ScalarGaussianCoordinates
  MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal

namespace MathlibExtTest.InformationTheory.ScalarGaussianKernelKL

/-- Scalar consistency: the vector closed form at dimension one, on the embedded input law, is the
scalar closed form, here at reference mean `2`, noise variance `3` and reference variance `5`. -/
example (μ : Measure ℝ) :
    gaussianKernelKLReal (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord 2)
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ) (!![5] : Matrix (Fin 1) (Fin 1) ℝ)
        (μ.map scalarCoord) =
      scalarGaussianKernelKLReal 2 3 5 μ :=
  gaussianKernelKLReal_scalarCoord 2 3 5 μ

/-- Scalar consistency on a point mass: the vector closed form at the embedded point mass is the
scalar Gaussian divergence of `N(4, 3)` from `N(1, 3)`, namely `3 / 2`. -/
example :
    gaussianKernelKLReal (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord 1)
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ) (!![3] : Matrix (Fin 1) (Fin 1) ℝ)
        ((Measure.dirac (4 : ℝ)).map scalarCoord) = 3 / 2 := by
  rw [gaussianKernelKLReal_scalarCoord, scalarGaussianKernelKLReal_dirac]
  norm_num

/-- Dirac evaluation of the closed form: equal variances and an input at the reference mean give
zero. -/
example : scalarGaussianKernelKLReal 1 2 2 (Measure.dirac 1) = 0 := by
  rw [scalarGaussianKernelKLReal_dirac]
  norm_num

/-- Dirac evaluation at the measure level: equal noise and reference variances and an input at the
reference mean give divergence zero. -/
example :
    klDiv ((Measure.dirac (1 : ℝ)) ⊗ₘ
          MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 2))
        ((Measure.dirac (1 : ℝ)).prod (gaussianReal 1 2)) = 0 := by
  rw [klDiv_compProd_gaussianNoiseKernel_dirac 1 2 2 (by norm_num) (by norm_num) 1]
  norm_num

/-- Dirac evaluation with a nonzero input mean: input `3`, reference `N(0, 1)`, noise variance
`1`. -/
example :
    klDiv ((Measure.dirac (3 : ℝ)) ⊗ₘ
          MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 1))
        ((Measure.dirac (3 : ℝ)).prod (gaussianReal 0 1)) =
      ENNReal.ofReal (9 / 2) :=
  klDiv_compProd_gaussianNoiseKernel_dirac_three

/-- The scalar kernel at identity gain is the Gaussian centered at the input. -/
example (x : ℝ) :
    MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 2) x = gaussianReal x 2 :=
  noiseKernel_id_gaussianReal_apply 2 x

end MathlibExtTest.InformationTheory.ScalarGaussianKernelKL
