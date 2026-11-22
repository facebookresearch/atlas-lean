/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 22 Problem 5.19: locally exceptional values
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Batteries.Util.ProofWanted

open scoped Topology

@[expose] public section

namespace MathlibExt.Analysis.AMR22Problem5019Wanted

/-! Source record `AMR-022-5019`. -/

namespace AMR22P5019

/-!
# Clause inventory for [AMR-022-5019] Problem 5.19 (E. F. Collingwood)

- Domain of meromorphicity: the unit disc `D`.
- Boundary set: the circumference `T`.
- Object: a function meromorphic in `D`, with poles in `D`, discrete,
  holomorphic off the poles, unbounded near each pole.
- Side condition: no asymptotic value, finite or infinite.
- Global value distribution: every Riemann-sphere value assumed infinitely
  often in the disc (finite values by infinite fibres, infinity by infinite
  pole set).
- Picard property quantified over every point of `T`.
- Picard point: all except perhaps two sphere values taken in every
  neighbourhood intersected with `D`.
- Question domain: a boundary point of `T`, a neighbourhood of it, and a
  sphere value omitted in that relative neighbourhood (locally exceptional).
-/

/-- Unit disc `D` in [AMR-022-5019] Problem 5.19. -/
def openUnitDisc : Set ℂ := Metric.ball 0 1

/-- Circumference `T` in [AMR-022-5019] Problem 5.19. -/
def unitCircle : Set ℂ := {z | ‖z‖ = 1}

/-- Meromorphic in `D` in [AMR-022-5019] Problem 5.19: poles lie in `D`,
discrete, complex-differentiable off the poles, unbounded near each pole. -/
def IsMeromorphicInDisc (f : ℂ → ℂ) (poles : Set ℂ) : Prop :=
  poles ⊆ openUnitDisc ∧ DiscreteTopology ↥poles ∧
    DifferentiableOn ℂ f (openUnitDisc \ poles) ∧
    ∀ z ∈ poles, ∀ M : ℝ, ∃ U ∈ 𝓝 z, ∀ w ∈ U \ poles, M ≤ ‖f w‖

/-- Finite asymptotic value in [AMR-022-5019] Problem 5.19: a continuous curve
in `D` off the poles tending to a point of `T` along which `f` tends to `w`. -/
def IsFiniteAsymptoticValue (f : ℂ → ℂ) (poles : Set ℂ) (w : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, Continuous γ ∧ (∀ t, γ t ∈ openUnitDisc \ poles) ∧
    ∃ ζ ∈ unitCircle, Filter.Tendsto γ Filter.atTop (𝓝 ζ) ∧
      Filter.Tendsto (fun t => f (γ t)) Filter.atTop (𝓝 w)

/-- Infinite asymptotic value in [AMR-022-5019] Problem 5.19: a continuous curve
in `D` off the poles tending to a point of `T` along which `‖f‖` tends to infinity. -/
def HasInfiniteAsymptoticValue (f : ℂ → ℂ) (poles : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, Continuous γ ∧ (∀ t, γ t ∈ openUnitDisc \ poles) ∧
    ∃ ζ ∈ unitCircle, Filter.Tendsto γ Filter.atTop (𝓝 ζ) ∧
      Filter.Tendsto (fun t => ‖f (γ t)‖) Filter.atTop Filter.atTop

/-- No asymptotic value in [AMR-022-5019] Problem 5.19. -/
def HasNoAsymptoticValue (f : ℂ → ℂ) (poles : Set ℂ) : Prop :=
  (∀ w : ℂ, ¬ IsFiniteAsymptoticValue f poles w) ∧
    ¬ HasInfiniteAsymptoticValue f poles

/-- Every value infinitely often in [AMR-022-5019] Problem 5.19: each finite
value has infinite fibre in `D` off the poles, and the pole set is infinite. -/
def TakesEveryValueInfinitelyOften (f : ℂ → ℂ) (poles : Set ℂ) : Prop :=
  (∀ a : ℂ, {z ∈ openUnitDisc \ poles | f z = a}.Infinite) ∧ poles.Infinite

/-- Picard boundary point in [AMR-022-5019] Problem 5.19: `ζ ∈ T` such that in
every neighbourhood `U` of `ζ`, all sphere values except at most two are taken
in `D ∩ U` (infinity via a pole, finite values via `f`). -/
def IsPicardPoint (f : ℂ → ℂ) (poles : Set ℂ) (ζ : ℂ) : Prop :=
  ζ ∈ unitCircle ∧ ∀ U ∈ 𝓝 ζ, ∃ omitted : Finset (Option ℂ), omitted.card ≤ 2 ∧
    ∀ w : Option ℂ, w ∉ omitted →
      match w with
      | none => ∃ z ∈ openUnitDisc ∩ U, z ∈ poles
      | some a => ∃ z ∈ openUnitDisc ∩ U, z ∉ poles ∧ f z = a

/-- Locally exceptional value in [AMR-022-5019] Problem 5.19: `ζ ∈ T` and a
sphere value omitted throughout some relative neighbourhood `D ∩ U`. -/
def IsLocallyExceptionalValue (f : ℂ → ℂ) (poles : Set ℂ) (ζ : ℂ)
    (w : Option ℂ) : Prop :=
  ζ ∈ unitCircle ∧ ∃ U ∈ 𝓝 ζ, match w with
    | none => ∀ z ∈ openUnitDisc ∩ U, z ∉ poles
    | some a => ∀ z ∈ openUnitDisc ∩ U, z ∉ poles → f z ≠ a

/-- [AMR-022-5019] Problem 5.19 (E. F. Collingwood), answered affirmatively by Eremenko
(Hayman-Lingham Update 5.19): does there exist a function meromorphic in `D` with no
asymptotic value, assuming every value infinitely often, Picard at every point of `T`,
possessing a locally exceptional value at some point of `T`? -/
def CollingwoodLocalExceptionProblem : Prop :=
  ∃ f : ℂ → ℂ, ∃ poles : Set ℂ, IsMeromorphicInDisc f poles ∧
    HasNoAsymptoticValue f poles ∧ TakesEveryValueInfinitelyOften f poles ∧
    (∀ ζ ∈ unitCircle, IsPicardPoint f poles ζ) ∧
    ∃ ζ ∈ unitCircle, ∃ w : Option ℂ, IsLocallyExceptionalValue f poles ζ w

end AMR22P5019
/--
Resolved true: Resolved affirmatively according to the list's own update: Hayman and Lingham
(arXiv:1809.07200v2, Update 5.19) report that Eremenko gave a strongly positive answer
(unpublished) by slightly modifying an example of Barth and Schneider, producing such a function
whose zeros and poles accumulate only at z = 1. Source: W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory (Fiftieth Anniversary Edition), arXiv:1809.07200v2, Update 5.19,
https://arxiv.org/abs/1809.07200v2. Moved from `OpenConjectures/Analysis/AMR22Problem5019`.
-/
public theorem_wanted CollingwoodLocalExceptionProblem_holds : AMR22P5019.CollingwoodLocalExceptionProblem

end MathlibExt.Analysis.AMR22Problem5019Wanted
