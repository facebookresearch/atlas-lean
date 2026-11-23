/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Talagrand's transport inequality for the Gaussian measure: wanted

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 22.1
and Example 22.15; M. Talagrand, Geom. Funct. Anal. 6 (1996) 587–600.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost)

namespace MathlibExt.Probability.TalagrandTransportWanted

/-- **Talagrand's transport inequality for the Gaussian measure.** Let `γ` be the standard
Gaussian measure on a finite-dimensional real inner product space `E`. For every probability
measure `μ` on `E` with finite second moment, `W_2(μ, γ)² ≤ 2 H_γ(μ)`, where
`H_γ(μ) = KL(μ ‖ γ)` is the relative entropy (`+∞` unless `μ ≪ γ`): `γ` satisfies `T_2(1)`,
with a constant independent of the dimension (C. Villani, *Optimal Transport: Old and New*,
Springer 2009, Example 22.15 with Definition 22.1; originally M. Talagrand, Geom. Funct. Anal.
6 (1996) 587–600). -/
theorem_wanted talagrand_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E) (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure E) < ∞) :
    wasserstein 2 μ ⟨stdGaussian E, inferInstance⟩ ^ (2 : ℝ) ≤
      2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E)

end MathlibExt.Probability.TalagrandTransportWanted
