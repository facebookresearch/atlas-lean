/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-6114: does the preimage of a regular curve under an analytic
conformal disc map necessarily have finite length?

A set is regular when its 1-dimensional Hausdorff measure inside any disc
of radius `r` is at most `C * r`. Conformal means holomorphic with nowhere
vanishing derivative on the unit disc and injective on the disc. Finite
length is finiteness of the 1-dimensional Hausdorff measure of the
preimage inside the disc.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open scoped ENNReal

namespace MathlibExt.Analysis.ConformalPreimageFiniteLengthWanted

/-! Source record `AMR-022-6114`. -/

/-- A set is regular when its 1-dimensional Hausdorff measure in every disc
of radius `r` is bounded by `C * r`. -/
def IsRegular (Gamma : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℂ) (r : ℝ), 0 < r →
    MeasureTheory.Measure.hausdorffMeasure 1 (Gamma ∩ Metric.ball c r) ≤
      ENNReal.ofReal (C * r)

/-- A regular curve: the trace of a continuous curve satisfying the
regularity bound of `IsRegular`. -/
def IsRegularCurve (Gamma : Set ℂ) : Prop :=
  IsRegular Gamma ∧
    ∃ (a b : ℝ) (γ : ℝ → ℂ), ContinuousOn γ (Set.Icc a b) ∧
      Gamma = γ '' Set.Icc a b

/-- [AMR-022-6114] Preimages of regular curves under analytic conformal disc
maps have finite length. Conformal includes global injectivity on the disc:
without it, `exp (-(1 + z) / (1 - z))` pulls the compact segment `[0, 1]`
back to infinitely many arcs whose lengths are asymptotic to `1 / (2|k|)`,
a set of infinite length, and `[0, 1]` is a regular curve. -/
def conjecture : Prop :=
  ∀ Gamma : Set ℂ, IsRegularCurve Gamma →
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, deriv f z ≠ 0) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) →
      MeasureTheory.Measure.hausdorffMeasure 1
        ((f ⁻¹' Gamma) ∩ Metric.ball (0 : ℂ) 1) < ∞

/--
Resolved true: Resolved affirmatively: Bishop and Jones (Harmonic measure and arclength, Ann. of
Math. 132 (1990) 511-547, Theorem 3) prove that for a connected Ahlfors-regular curve Γ there is
C_Γ with length(Φ^{-1}(Γ ∩ Ω)) < C_Γ for every Riemann map Φ of the disc onto a simply connected
domain Ω. A univalent f on the disc is such a map onto f(D), so f^{-1}(Γ) has finite length.
Source: C. J. Bishop, P. W. Jones, Harmonic measure and arclength, Ann. of Math. 132 (1990)
511-547, https://doi.org/10.2307/1971428. Moved from
`OpenConjectures/Analysis/ConformalPreimageFiniteLength`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ConformalPreimageFiniteLengthWanted
