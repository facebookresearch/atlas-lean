/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

import MathlibExt.Probability.Reliability.FailureBracket

/-!
# Failure bracket checks

Focused checks for `MathlibExt.Probability.Reliability.FailureBracket`:
at `delta = 0` with `B = univ` the exceptional term vanishes and both
sides collapse to the same failure event; failure at equality is
included.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory Set Reliability

/-- With `B = univ` and `delta = 0`, upper bracket is equality-tight for
a Dirac measure. -/
example (L : Bool → ℝ) (ω : Bool) :
    (Measure.dirac ω) {x : Bool | L x ≤ 0}
      ≤ (Measure.dirac ω) {x : Bool | L x ≤ 0} + (Measure.dirac ω) (Set.univ : Set Bool)ᶜ :=
  measure_failure_bracket_upper (Measure.dirac ω) L L Set.univ 0 (fun x _ => by simp)

/-- Lower bound with positive `delta` and a nontrivial exceptional set,
through the public theorem. -/
example (ω : Bool) :
    (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ -1}
      ≤ (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ 0}
        + (Measure.dirac ω) ({true} : Set Bool)ᶜ :=
  measure_failure_bracket_lower (Measure.dirac ω) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    {true} 1 (fun x _ => by simp)

/-- Combined subtracted bracket, through the public theorem. -/
example (ω : Bool) :
    (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ -1}
        - (Measure.dirac ω) ({true} : Set Bool)ᶜ
      ≤ (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ 0}
    ∧ (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ 0}
      ≤ (Measure.dirac ω) {x : Bool | (0 : Bool → ℝ) x ≤ 1}
        + (Measure.dirac ω) ({true} : Set Bool)ᶜ :=
  measure_failure_bracket (Measure.dirac ω) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    {true} 1 (fun x _ => by simp)

/-- Failure at equality: `g = 0` is in the failure event. -/
example (ω : Bool) : ω ∈ {x : Bool | (0 : Bool → ℝ) x ≤ 0} := by
  simp
