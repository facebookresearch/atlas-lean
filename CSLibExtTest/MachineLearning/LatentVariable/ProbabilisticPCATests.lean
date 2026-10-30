/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ProbabilisticPCA

/-!
# Probabilistic PCA tests

Closed checks: the marginal theorems instantiated for a two-dimensional latent variable observed
in three dimensions, for isotropic (probabilistic PCA) and diagonal (factor analysis) noise. The
definitions are measures and not executable.
-/

namespace Cslib.MachineLearning.LatentVariable.ProbabilisticPCA

open MeasureTheory ProbabilityTheory Matrix

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} {E : Ω → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 ((1 / 4 : ℝ) • 1)) P) (hind : IndepFun Z E P)
    (W : Matrix (Fin 3) (Fin 2) ℝ) (μ : EuclideanSpace ℝ (Fin 3)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) =
      multivariateGaussian μ (W * Wᵀ + (1 / 4 : ℝ) • 1) :=
  ppca_map_eq (by norm_num) hZ hE hind W μ

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} {E : Ω → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 (diagonal ![1, 2, 3])) P) (hind : IndepFun Z E P)
    (W : Matrix (Fin 3) (Fin 2) ℝ) (μ : EuclideanSpace ℝ (Fin 3)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) =
      multivariateGaussian μ (W * Wᵀ + diagonal ![1, 2, 3]) :=
  factorAnalysis_map_eq (fun i => by fin_cases i <;> norm_num) hZ hE hind W μ

#print axioms map_eq_multivariateGaussian

end Cslib.MachineLearning.LatentVariable.ProbabilisticPCA
