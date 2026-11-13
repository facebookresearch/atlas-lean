/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded Analytic Function with Infinite Radial Lengths
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.BoundedAnalyticInfiniteRadialLengthWanted

open MeasureTheory Metric

/-! Source record `AMR-022-5075` (dataset id 2305075), from ulamai/UnsolvedMath
(Research Problems in Function Theory, Problem 5.75; W. Rudin, communicated by
K. F. Barth): "Does there exist a bounded analytic function in 𝔻 such that the
image of every radius has infinite length?"

Analyticity in 𝔻 is complex differentiability on the open unit ball (the standard Mathlib
encoding), boundedness is a uniform bound `‖f z‖ ≤ M` on the ball, and the image of the radius at
angle `θ` is the curve `r ↦ f(r e^{iθ})` (`radial f θ`). Its length is encoded as
non-integrability of the speed on `(0, 1)`, which for these smooth radial curves of a holomorphic
function is equivalent to infinite length. -/

/-- The radial curve of `f` at angle `θ`: `r ↦ f(r e^{iθ})`. -/
noncomputable def radial (f : ℂ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  fun r => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

/-- The image of the radius at angle `θ` has infinite length, i.e. the speed
is not integrable on `(0, 1)`. -/
def HasInfiniteRadialLength (f : ℂ → ℂ) (θ : ℝ) : Prop :=
  ¬IntegrableOn (fun r => ‖deriv (radial f θ) r‖) (Set.Ioo (0 : ℝ) 1) volume

/-- Rudin–Barth problem: there is a bounded function analytic in the disc
whose every radial image has infinite length. -/
def conjecture : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (0 : ℂ) 1) ∧
    (∃ M : ℝ, ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → ‖f z‖ ≤ M) ∧
    ∀ θ : ℝ, HasInfiniteRadialLength f θ

/--
Resolved false: Resolved false. Bourgain (On the radial variation of bounded analytic functions
on the disc, Duke Math. J. 69 (1993) 671-682, Theorem 1) proves that for every bounded analytic
function on the disc the set of directions with finite radial variation is nonempty (of
Hausdorff dimension 1), so no bounded analytic function has radial images of infinite length in
every direction. Source: J. Bourgain, On the radial variation of bounded analytic functions on
the disc, Duke Math. J. 69 (1993) 671-682, https://doi.org/10.1215/S0012-7094-93-06928-1. Moved
from `OpenConjectures/Analysis/BoundedAnalyticInfiniteRadialLength`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.BoundedAnalyticInfiniteRadialLengthWanted
