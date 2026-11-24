/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Keyfitz's life-table entropy: `d e₀ / dδ = -H e₀` for a proportional change in mortality

For a mortality rate `μ ≥ 0` on `[0, ω]`, survival is `l(x) = exp(-∫_0^x μ)` and life
expectancy at birth is `e₀ = ∫_0^ω l`. Changing every age-specific rate by the same factor,
`μ* = (1 + δ) μ`, gives `l* = l^{1+δ}`. Keyfitz (1977) expanded `e₀*` to first order:
`e₀*/e₀ = 1 - δ H`, with the life-table entropy `H = -∫_0^ω l ln l / ∫_0^ω l`. The exact form
recorded here is that `δ ↦ e₀(δ)` is differentiable at `0` with derivative `∫_0^ω l ln l`,
which is `-H e₀`. As in Keyfitz, integrals run to the last age `ω`.

`Domains.Biology.Demography.LifeTable` lists life expectancy as not covered.

Sources: N. Keyfitz, "What difference would it make if cancer were eradicated? An examination
of the Taeuber paradox", Demography 14 (1977) 411–418, pp. 412–413.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.KeyfitzEntropyWanted

open MeasureTheory Real

/-- **Survival** under the mortality rate `μ`: `l(x) = exp(-∫_0^x μ)`. -/
noncomputable def survival (μ : ℝ → ℝ) (x : ℝ) : ℝ :=
  exp (-∫ a in (0 : ℝ)..x, μ a)

/-- **Life expectancy at birth** for survival `l` and last age `ω`: `e₀ = ∫_0^ω l`. -/
noncomputable def lifeExpectancy (ω : ℝ) (l : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..ω, l x

/-- **Keyfitz's life-table entropy** `H = -∫_0^ω l ln l / ∫_0^ω l`. -/
noncomputable def keyfitzEntropy (ω : ℝ) (l : ℝ → ℝ) : ℝ :=
  -(∫ x in (0 : ℝ)..ω, l x * log (l x)) / lifeExpectancy ω l

/-- **Keyfitz's entropy formula** (Keyfitz 1977, pp. 412–413). Let `ω > 0` and let `μ ≥ 0` be
integrable on `[0, ω]`. Then the life expectancy under the proportionally changed rates
`(1 + δ) μ` is differentiable in `δ` at `δ = 0`, with derivative `-H e₀`, where `e₀` and `H`
are the life expectancy and the life-table entropy of the original survival curve. Hence
`e₀(δ)/e₀ = 1 - δ H + o(δ)`.

Source: Keyfitz (1977), pp. 412–413. -/
public theorem_wanted hasDerivAt_lifeExpectancy_proportional {ω : ℝ} (hω : 0 < ω)
    {μ : ℝ → ℝ} (hμ : IntervalIntegrable μ volume 0 ω) (hμ0 : ∀ x ∈ Set.Icc 0 ω, 0 ≤ μ x) :
    HasDerivAt (fun δ => lifeExpectancy ω (survival (fun a => (1 + δ) * μ a)))
      (-(keyfitzEntropy ω (survival μ) * lifeExpectancy ω (survival μ))) 0

end WantedExt.Biology.Ecology.KeyfitzEntropyWanted
