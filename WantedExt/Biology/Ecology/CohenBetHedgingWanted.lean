/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cohen's bet-hedging germination: dormancy is favored if and only if `s E[1/Y] > 1`

A seed bank grows by `n(t + 1) = (H Yₜ + (1 - H) s) n(t)`, where a fraction `H ∈ [0, 1]` of seeds
germinates and yields `Yₜ` seeds each, the rest stays dormant with survival `0 < s < 1`, and the
yields `Yₜ` are independent and identically distributed. The long-run growth rate is
`ρ(H) = E[log(H Y + (1 - H) s)]`. Cohen (1966), as presented by Ellner, showed that `ρ` is
concave, strictly so unless `Y = s` almost surely, and that its left derivative at
`H = 1` is `1 - s E[1/Y]`; hence full germination is optimal if and only if `s E[1/Y] ≤ 1`, and
bet-hedging dormancy (`H* < 1`) is favored if and only if `s E[1/Y] > 1`.

Recorded here: the optimality criterion and the strict concavity, for a yield `Y > 0` with
`log Y` and `1 / Y` integrable (so that `ρ` is finite on `[0, 1]`). The primary was not read; the
statement follows Ellner's chapter on bet hedging (eqs. 2.1 and 2.25).

Sources: D. Cohen, "Optimizing reproduction in a randomly varying environment", J. Theor. Biol.
12 (1966) 119–129, doi:10.1016/0022-5193(66)90188-3; S. P. Ellner, lecture notes, chapter 2
"Bet hedging", eqs. 2.1 and 2.25.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.CohenBetHedgingWanted

open MeasureTheory

/-- The long-run growth rate `ρ(H) = E[log(H Y + (1 - H) s)]` of the seed bank with germination
fraction `H`, dormant survival `s` and random yield `Y`. -/
noncomputable def growthRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)
    (s H : ℝ) : ℝ :=
  ∫ ω, Real.log (H * Y ω + (1 - H) * s) ∂μ

/-- **Cohen's germination criterion** (Cohen 1966; Ellner, eq. 2.25): let `μ` be a probability
measure, `0 < s < 1`, and `Y` a measurable yield with `Y > 0` everywhere such that `log Y` and
`1 / Y` are integrable. Then full germination maximizes the long-run growth rate, i.e.
`ρ(H) ≤ ρ(1)` for every `H ∈ [0, 1]`, if and only if `s E[1/Y] ≤ 1`. Equivalently, some
germination fraction `H < 1` does strictly better than `H = 1` if and only if `s E[1/Y] > 1`.

Sources: Cohen (1966); Ellner, chapter 2, eqs. 2.1 and 2.25. -/
public theorem_wanted full_germination_optimal_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) (Y : Ω → ℝ)
    (hY : Measurable Y) (hpos : ∀ ω, 0 < Y ω) (hlog : Integrable (fun ω => Real.log (Y ω)) μ)
    (hinv : Integrable (fun ω => (Y ω)⁻¹) μ) :
    (∀ H : ℝ, 0 ≤ H → H ≤ 1 → growthRate μ Y s H ≤ growthRate μ Y s 1) ↔
      s * ∫ ω, (Y ω)⁻¹ ∂μ ≤ 1

/-- **Strict concavity of the long-run growth rate** (Cohen 1966; Ellner, chapter 2): under the
hypotheses of the criterion (`μ` a probability measure, `0 < s < 1`, `Y` measurable with `Y > 0`
and `log Y`, `1 / Y` integrable), if moreover `Y` is not almost surely equal to the dormant
survival `s` (it is not the case that `Y = s` almost everywhere), then
`ρ(H) = E[log(H Y + (1 - H) s)]` is strictly concave on `[0, 1]`. (If `Y = s` almost surely,
`ρ` is the constant `log s`.)

Sources: Cohen (1966); Ellner, chapter 2. -/
public theorem_wanted growthRate_strictConcaveOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) (Y : Ω → ℝ)
    (hY : Measurable Y) (hpos : ∀ ω, 0 < Y ω) (hlog : Integrable (fun ω => Real.log (Y ω)) μ)
    (hinv : Integrable (fun ω => (Y ω)⁻¹) μ) (hns : ¬ Y =ᵐ[μ] fun _ => s) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (growthRate μ Y s)

end WantedExt.Biology.Ecology.CohenBetHedgingWanted
