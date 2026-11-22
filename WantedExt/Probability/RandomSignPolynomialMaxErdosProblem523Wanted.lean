/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximum of a random `±1` polynomial on the circle (Erdős Problem 523)

Erdős Problem 523: for independent uniform signs `εₖ`, is there `C > 0` such that almost surely
`max_{|z| = 1} |∑_{k ≤ n} εₖ z ^ k| = (C + o(1)) √(n log n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import WantedExt.Probability.RandomSignSequenceShared

@[expose] public section

namespace MathlibExt.Probability.RandomSignPolynomialMaxErdosProblem523Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #523, https://www.erdosproblems.com/523 (status
PROVED). UnsolvedMath record UM-30006916 (`EP-523`), dataset ulamai/UnsolvedMath v1.8.0.

Random signs are any sequence of measurable, independent, almost surely `±1` random variables, each
equal to `1` with probability `1/2`, on an arbitrary probability space. The maximum over the circle
is a supremum over `Metric.sphere 0 1`; `(C + o(1)) √(n log n)` is convergence of the ratio to `C`.
The target asks for some `C`; Halász proved `C = 1`.
-/

open MathlibExt.Probability.RandomSignSequenceShared

/-- `max_{|z| = 1} |∑_{k ≤ n} ε k ω z ^ k|`. -/
noncomputable def signPolynomialMax {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  ⨆ z : Metric.sphere (0 : ℂ) 1, ‖∑ k ∈ Finset.range (n + 1), (ε k ω : ℂ) * (z : ℂ) ^ k‖

open MeasureTheory in
/-- Erdős Problem 523: there is `C > 0` such that for independent uniform random signs `εₖ`,
almost surely `max_{|z| = 1} |∑_{k ≤ n} εₖ z ^ k| = (C + o(1)) √(n log n)`. -/
def randomSignPolynomialMaxAsymptotic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ε : ℕ → Ω → ℝ), IsRandomSignSequence ε →
      ∀ᵐ ω, Filter.Tendsto (fun n : ℕ => signPolynomialMax ε ω n / Real.sqrt (n * Real.log n))
        Filter.atTop (nhds C)

/--
Resolved true: Halász proved the almost sure asymptotic with `C = 1`; Salem and Zygmund had the
order of magnitude `√(n log n)`. Source: T. F. Bloom, Erdős Problems, Problem #523,
https://www.erdosproblems.com/523 (status PROVED); resolution: G. Halász, On a result of Salem and
Zygmund concerning random polynomials, Studia Sci. Math. Hungar. (1973), 369-377,
erdosproblems.com/523: settled by Halász, true with C = 1, https://www.erdosproblems.com/523.
-/
public theorem_wanted randomSignPolynomialMaxAsymptotic_holds : randomSignPolynomialMaxAsymptotic

end MathlibExt.Probability.RandomSignPolynomialMaxErdosProblem523Wanted
