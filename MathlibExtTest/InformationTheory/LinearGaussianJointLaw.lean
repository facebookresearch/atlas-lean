/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianJointLaw

@[expose] public section

open MathlibExt.InformationTheory.LinearGaussianJointLaw MeasureTheory ProbabilityTheory Matrix

namespace MathlibExtTest.InformationTheory.LinearGaussianJointLaw

/-- The conditional law of the channel output is the noise kernel. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Matrix (Fin 2) (Fin 2) ℝ)
    {R : Matrix (Fin 2) (Fin 2) ℝ} {X : Ω → EuclideanSpace ℝ (Fin 2)}
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R) :
    condDistrib (fun ω => toEuclideanLin H (X ω) + Z ω) X μ =ᵐ[μ.map X]
      MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) :=
  condDistrib_eq_noiseKernel H hX hZ hind hZlaw

end MathlibExtTest.InformationTheory.LinearGaussianJointLaw
