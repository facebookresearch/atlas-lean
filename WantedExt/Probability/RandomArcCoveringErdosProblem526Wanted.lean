/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering the circle by random arcs (Erdős Problem 526)

Erdős Problem 526 (Dvoretzky): for `aₙ ≥ 0` with `aₙ → 0` and `∑ aₙ = ∞`, find a necessary and
sufficient condition for independent uniform random arcs of lengths `aₙ` to cover the circle almost
surely.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace MathlibExt.Probability.RandomArcCoveringErdosProblem526Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #526, https://www.erdosproblems.com/526 (status
SOLVED). UnsolvedMath record UM-30006918 (`EP-526`), dataset ulamai/UnsolvedMath v1.8.0.

The circle has length `1` (`AddCircle 1`), as the thresholds `aₙ = (1 ± c)/n` on erdosproblems.com
require. Shepp's condition is for non-increasing lengths below `1`; the covering event does not
depend on the order of the lengths, so non-increasing is no loss, and `ℓ 0 < 1` is needed (with `ℓ 0
= 1` the circle is covered while the series can converge). Arcs are open; open and closed arcs cover
alike almost surely, since every arc endpoint is almost surely inside another arc.
-/

/-- The open arc of length `ℓ` starting at `x` on the circle `ℝ / ℤ` of length `1`. -/
def openArc (x : AddCircle (1 : ℝ)) (ℓ : ℝ) : Set (AddCircle (1 : ℝ)) :=
  (fun t : ℝ => x + (t : AddCircle (1 : ℝ))) '' Set.Ioo 0 ℓ

open MeasureTheory ProbabilityTheory in
/-- Erdős Problem 526 (Dvoretzky), Shepp's answer: for non-increasing lengths
`1 > ℓ 0 ≥ ℓ 1 ≥ ⋯ ≥ 0` with `ℓ n → 0` and `∑ ℓ n = ∞`, independent uniform random open arcs of
lengths `ℓ n` on the circle of length `1` cover it almost surely iff
`∑ₙ (n + 1) ^ (-2) exp(ℓ 0 + ⋯ + ℓ n) = ∞`. -/
def randomArcsCoverIffShepp : Prop :=
  ∀ ℓ : ℕ → ℝ, (∀ n, 0 ≤ ℓ n) → Antitone ℓ → ℓ 0 < 1 →
    Filter.Tendsto ℓ Filter.atTop (nhds 0) → ¬ Summable ℓ →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (X : ℕ → Ω → AddCircle (1 : ℝ)), (∀ n, Measurable (X n)) → iIndepFun X →
      (∀ n, Measure.map (X n) volume = volume) →
      ((∀ᵐ ω, ∀ x : AddCircle (1 : ℝ), ∃ n, x ∈ openArc (X n ω) (ℓ n)) ↔
        ¬ Summable fun n : ℕ => Real.exp (∑ i ∈ Finset.range (n + 1), ℓ i) / ((n : ℝ) + 1) ^ 2)

/--
Resolved true: Shepp proved that for lengths `1 > ℓ₁ ≥ ℓ₂ ≥ ⋯ > 0` on the circle of length `1` the
circle is covered almost surely iff `∑ₙ n ^ (-2) exp(ℓ₁ + ⋯ + ℓₙ) = ∞`. Source: T. F. Bloom, Erdős
Problems, Problem #526, https://www.erdosproblems.com/526 (status SOLVED); resolution: L. A. Shepp,
Covering the circle with random arcs, Israel J. Math. 11 (1972), 328-345, erdosproblems.com/526 and
Encyclopedia of Mathematics, Dvoretzky problem (J.-P. Kahane): for 1 > l_1 ≥ l_2 ≥ ... > 0 on the
circle of length 1, covering holds iff ∑ n^{-2} exp(l_1 + ... + l_n) = ∞,
https://encyclopediaofmath.org/wiki/Dvoretzky_problem.
-/
public theorem_wanted randomArcsCoverIffShepp_holds : randomArcsCoverIffShepp

end MathlibExt.Probability.RandomArcCoveringErdosProblem526Wanted
