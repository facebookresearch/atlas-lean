/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1126
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Filter

namespace MathlibExt.Analysis.ErdosProblem1126Wanted

/-! Source record `FC-ErdosProblem1126`, ported from FormalConjectures
`ErdosProblems/1126.lean` (`theorem erdos_1126`) and checked against
erdosproblems.com/1126. The `answer(True)` wrapper is dropped. Status:
resolved true (de Bruijn; Jurkat). -/

/-- Almost-everywhere Cauchy implies almost-everywhere additive. -/
def conjecture : Prop :=
  ∀ (f : ℝ → ℝ),
    (∀ᵐ (p : ℝ × ℝ) ∂(MeasureTheory.volume.prod MeasureTheory.volume),
      f (p.1 + p.2) = f p.1 + f p.2) →
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂MeasureTheory.volume, f x = h x)

/--
Resolved true: Resolved affirmatively (de Bruijn [dB66]; Jurkat [Ju65]), per
erdosproblems.com/1126. Source: de Bruijn [dB66] and Jurkat [Ju65], independently, per
erdosproblems.com/1126, https://www.erdosproblems.com/1126. Moved from
`OpenConjectures/Analysis/ErdosProblem1126`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosProblem1126Wanted
