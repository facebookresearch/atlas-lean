/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gross' logarithmic Sobolev inequality for the Gaussian measure: wanted

L. Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975), in the form of
M. Ledoux, *Heat flows, geometric and functional inequalities*, Proceedings of the ICM, Seoul
2014, Theorem 2.1, whose proof (after Bakry and Émery) interpolates along the heat semigroup.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ContDiff

namespace MathlibExt.Probability.GaussianLogSobolevWanted

/-- **Gross' logarithmic Sobolev inequality.** Let `γ` be the standard Gaussian measure on a
finite-dimensional real inner product space `E`. For every smooth (`C^∞`) positive `f` with
`∫ f dγ = 1`,
`∫ f log f dγ ≤ ½ ∫ |∇f|² / f dγ`,
where the left side is the relative entropy `KL(f γ ‖ γ)` (M. Ledoux, *Heat flows, geometric
and functional inequalities*, Proceedings of the ICM, Seoul 2014, Theorem 2.1; originally
L. Gross, Amer. J. Math. 97 (1975)). The constant does not depend on the dimension. -/
theorem_wanted klDiv_withDensity_stdGaussian_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfint : ∫ x, f x ∂(stdGaussian E) = 1) :
    klDiv ((stdGaussian E).withDensity fun x => ENNReal.ofReal (f x)) (stdGaussian E) ≤
      (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂(stdGaussian E)

end MathlibExt.Probability.GaussianLogSobolevWanted
