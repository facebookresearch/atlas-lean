/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Convergent points of random power series (Erdős Problem 527)

Erdős Problem 527: if `aₙ ∈ ℝ`, `∑ |aₙ| ^ 2 = ∞` and `|aₙ| = o(1/√n)`, is it true that for almost
all signs `εₙ = ±1` some `z` with `|z| = 1` makes `∑ εₙ aₙ z ^ n` converge?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import WantedExt.Probability.RandomSignSequenceShared

@[expose] public section

namespace MathlibExt.Probability.RandomPowerSeriesConvergentPointErdosProblem527Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #527, https://www.erdosproblems.com/527 (status
PROVED). UnsolvedMath record UM-30006919 (`EP-527`), dataset ulamai/UnsolvedMath v1.8.0.

Random signs are any sequence of measurable, independent, almost surely `±1` random variables, each
equal to `1` with probability `1/2`, on an arbitrary probability space. Convergence is convergence
of partial sums (not unconditional summability). No monotonicity of `|aₙ|` is assumed.
-/

open MathlibExt.Probability.RandomSignSequenceShared

open MeasureTheory in
/-- Erdős Problem 527: if `aₙ ∈ ℝ` with `∑ aₙ ^ 2 = ∞` and `aₙ = o(n ^ (-1/2))`, then for almost
every choice of independent uniform signs `εₙ` there is `z` with `|z| = 1` at which
`∑ₙ εₙ aₙ z ^ n` converges (its partial sums have a limit). -/
def randomSeriesHasConvergentPoint : Prop :=
  ∀ a : ℕ → ℝ, ¬ Summable (fun n => a n ^ 2) →
    (fun n : ℕ => a n) =o[Filter.atTop] (fun n : ℕ => 1 / Real.sqrt n) →
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (ε : ℕ → Ω → ℝ), IsRandomSignSequence ε →
      ∀ᵐ ω, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ L : ℂ, Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, ((ε n ω * a n : ℝ) : ℂ) * z ^ n) Filter.atTop (nhds L)

/--
Resolved true: Michelen and Sawhney proved that for complex `aₙ = o(1/√n)` the set of `|z| = 1`
where the series converges almost surely has Hausdorff dimension `1`, in particular is nonempty;
Dvoretzky and Erdős showed `|aₙ| ≫ 1/√n` gives divergence everywhere. Source: T. F. Bloom, Erdős
Problems, Problem #527, https://www.erdosproblems.com/527 (status PROVED); resolution: M. Michelen
and M. Sawhney, Convergent points for random power series on the unit circle, arXiv:2509.02729
(2025), abstract and erdosproblems.com/527: if a_n = o(1/√n) the set of convergent points on |z| = 1
almost surely has Hausdorff dimension 1, https://arxiv.org/abs/2509.02729.
-/
public theorem_wanted randomSeriesHasConvergentPoint_holds : randomSeriesHasConvergentPoint

end MathlibExt.Probability.RandomPowerSeriesConvergentPointErdosProblem527Wanted
