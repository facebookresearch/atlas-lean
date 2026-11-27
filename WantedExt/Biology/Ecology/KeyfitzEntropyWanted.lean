/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Keyfitz's life-table entropy: `d e₀ / dδ = -H e₀` for a proportional change in mortality

For a mortality rate `μ ≥ 0` on `[0, ∞)`, survival is `l(x) = exp(-∫_0^x μ)` and life
expectancy at birth is `e₀ = ∫_0^∞ l`. Changing every age-specific rate by the same factor,
`μ* = (1 + δ) μ`, gives `l* = l^{1+δ}`. Keyfitz (1977) expanded `e₀*` to first order:
`e₀*/e₀ = 1 - δ H`, with the life-table entropy `H = -∫_0^∞ l ln l / ∫_0^∞ l`. The exact form
recorded here is that `δ ↦ e₀(δ)` is differentiable at `0` with derivative `∫_0^∞ l ln l`,
which is `-H e₀`. As in Fernandez and Beltrán-Sánchez (2015, §2.1), integrals run over
`[0, ∞)`. A mortality rate bounded below by a positive constant beyond some age makes `l` decay
exponentially, which keeps `∫_0^∞ l^{1+δ}` finite for `δ` near `0`.

`Domains.Biology.Demography.LifeTable` lists life expectancy as not covered.

Sources: N. Keyfitz, "What difference would it make if cancer were eradicated? An examination
of the Taeuber paradox", Demography 14 (1977) 411–418, pp. 412–413; O. E. Fernandez and
H. Beltrán-Sánchez, "The entropy of the life table: A reappraisal", Theor. Popul. Biol. 104
(2015) 26–45, §2.1, eqs. (2.1)–(2.4), and §2.5, eq. (2.13).
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

/-- **Life expectancy at birth** for survival `l`: `e₀ = ∫_0^∞ l`. -/
noncomputable def lifeExpectancy (l : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, l x

/-- **Keyfitz's life-table entropy** `H = -∫_0^∞ l ln l / ∫_0^∞ l`. -/
noncomputable def keyfitzEntropy (l : ℝ → ℝ) : ℝ :=
  -(∫ x in Set.Ioi 0, l x * log (l x)) / lifeExpectancy l

/-- **Keyfitz's entropy formula** (Keyfitz 1977; Fernandez and Beltrán-Sánchez 2015, §2.1). Let
`μ ≥ 0` be integrable on every interval `[0, x]` and bounded below by a constant `c > 0` beyond
some age. Then the life expectancy `∫_0^∞ l^{1+δ}` under the proportionally changed rates
`(1 + δ) μ` is differentiable in `δ` at `δ = 0`, with derivative `-H e₀`, where `e₀` and `H`
are the life expectancy and the life-table entropy of the original survival curve, integrals
running over `[0, ∞)`. Hence `e₀(δ)/e₀ = 1 - δ H + o(δ)`.

Sources: Fernandez and Beltrán-Sánchez (2015), §2.1, eqs. (2.3)–(2.4), and §2.5, eq. (2.13);
Keyfitz (1977), pp. 412–413. -/
public theorem_wanted hasDerivAt_lifeExpectancy_proportional {μ : ℝ → ℝ}
    (hμ : ∀ x, 0 ≤ x → IntervalIntegrable μ volume 0 x) (hμ0 : ∀ x, 0 ≤ x → 0 ≤ μ x)
    (hμc : ∃ c > 0, ∃ A, ∀ x, A ≤ x → c ≤ μ x) :
    HasDerivAt (fun δ => lifeExpectancy (survival (fun a => (1 + δ) * μ a)))
      (-(keyfitzEntropy (survival μ) * lifeExpectancy (survival μ))) 0

end WantedExt.Biology.Ecology.KeyfitzEntropyWanted
