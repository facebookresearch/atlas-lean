/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.FunctionalInequalities.OttoVillani
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The HWI inequality: wanted

F. Otto and C. Villani (*Generalization of an inequality by Talagrand and links with the
logarithmic Sobolev inequality*, J. Funct. Anal. 173 (2000), 361–400) used Otto's formal
Riemannian structure on the Wasserstein space to show that the logarithmic Sobolev inequality
implies Talagrand's transport inequality with the same constant, and proved the HWI inequality
linking relative entropy (H), Wasserstein distance (W) and Fisher information (I).

The Otto–Villani theorem is proved in
`MathlibExt.Probability.FunctionalInequalities.OttoVillani`. The HWI inequality under the
curvature condition `CD(0, ∞)` follows M. Ledoux, *Heat flows, geometric and functional
inequalities*, Proceedings of the ICM, Seoul 2014, Theorem 4.1, specialized to `ℝⁿ` with the measure
`e^{-V} dx`, where `CD(0, ∞)` means that `V` is convex.
-/

@[expose] public section

open MeasureTheory InformationTheory
open scoped ENNReal ContDiff

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein)

namespace MathlibExt.Probability.OttoVillaniWanted

/-- **HWI inequality (Otto–Villani), nonnegative curvature.** Let `V : E → ℝ` be a smooth
(`C^∞`) convex function on a finite-dimensional real inner product space with `μ = e^{-V} dx` a
probability measure. For every smooth (`C^∞`) positive `f` with `∫ f dμ = 1`, writing `ν = f μ`,

`∫ f log f dμ ≤ W₂(ν, μ) · (∫ |∇f|² / f dμ)^{1/2}`,

relative entropy `H = KL(ν ‖ μ)` bounded by the Wasserstein distance `W` times the square root
of the Fisher information `I` (M. Ledoux, *Heat flows, geometric and functional inequalities*,
Proceedings of the ICM, Seoul 2014, Theorem 4.1, under `CD(0, ∞)`, which on `ℝⁿ` with
`e^{-V} dx` is the convexity of `V`; originally F. Otto and C. Villani, J. Funct. Anal. 173
(2000)). -/
theorem_wanted klDiv_le_wasserstein_mul_sqrt_fisher {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : E → ℝ} (hV : ContDiff ℝ ∞ V) (hVconv : ConvexOn ℝ Set.univ V)
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = volume.withDensity fun x => ENNReal.ofReal (Real.exp (-V x)))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfint : ∫ x, f x ∂(μ : Measure E) = 1)
    (ν : ProbabilityMeasure E)
    (hν : (ν : Measure E) = (μ : Measure E).withDensity fun x => ENNReal.ofReal (f x)) :
    klDiv (ν : Measure E) (μ : Measure E) ≤
      wasserstein 2 ν μ *
        (∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂(μ : Measure E)) ^ (1 / 2 : ℝ)

end MathlibExt.Probability.OttoVillaniWanted
