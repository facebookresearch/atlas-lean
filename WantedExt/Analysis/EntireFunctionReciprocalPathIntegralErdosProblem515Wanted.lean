/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Paths to infinity with integrable `|f| ^ (-λ)` (Erdős Problem 515)

Erdős Problem 515: for an entire `f` that is not a polynomial, is there a locally rectifiable path
`C` to `∞` with `∫_C |f(z)| ^ (-λ) |dz| < ∞` for every `λ > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

namespace MathlibExt.Analysis.EntireFunctionReciprocalPathIntegralErdosProblem515Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #515, https://www.erdosproblems.com/515 (status
PROVED). UnsolvedMath record UM-30006912 (`EP-515`), dataset ulamai/UnsolvedMath v1.8.0.

The path is parametrized by arc length (`γ : [0, ∞) → ℂ` with the variation of `γ` on `[s, t]` equal
to `t - s`), so the line integral is `∫₀^∞ |f(γ t)| ^ (-λ) dt`; any locally rectifiable path to `∞`
has such a parametrization. One path serves every `λ`.
-/

/-- Erdős Problem 515: for every entire `f` that is not a polynomial there is a locally rectifiable
path to `∞`, parametrized by arc length `γ : [0, ∞) → ℂ`, with
`∫_γ |f(z)| ^ (-λ) |dz| = ∫₀^∞ |f(γ t)| ^ (-λ) dt < ∞` for every `λ > 0`. -/
def pathWithFiniteReciprocalIntegrals : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
    ∃ γ : ℝ → ℂ,
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → eVariationOn γ (Set.Icc s t) = ENNReal.ofReal (t - s)) ∧
      Filter.Tendsto (fun t => ‖γ t‖) Filter.atTop Filter.atTop ∧
      ∀ lam : ℝ, 0 < lam →
        MeasureTheory.IntegrableOn (fun t => ‖f (γ t)‖ ^ (-lam)) (Set.Ici 0)

/--
Resolved true: Lewis, Rossi and Weitsman proved it (for `e ^ u` with `u` subharmonic, so for `|f| =
e ^ (log |f|)`); Huber had a path `C_λ` for each single `λ`, and Zhang the finite-order case.
Source: T. F. Bloom, Erdős Problems, Problem #515, https://www.erdosproblems.com/515 (status
PROVED); resolution: J. Lewis, J. Rossi and A. Weitsman, On the growth of subharmonic functions
along paths, Ark. Mat. (1984), 109-119, erdosproblems.com/515: true; finite order by Zhang (1977),
general case by Lewis, Rossi and Weitsman (for e^u, u subharmonic),
https://www.erdosproblems.com/515.
-/
public theorem_wanted pathWithFiniteReciprocalIntegrals_holds : pathWithFiniteReciprocalIntegrals

end MathlibExt.Analysis.EntireFunctionReciprocalPathIntegralErdosProblem515Wanted
