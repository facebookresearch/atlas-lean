/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The war of attrition: no pure ESS, and the exponential persistence strategy

In Maynard Smith's war of attrition (1974, §3) over a resource of value `v > 0`, each contestant
chooses the cost `m ≥ 0` it is prepared to pay, linear in display time. If `m₁ > m₂` the first
gets `v - m₂` and the second `-m₂`; equal choices split the resource, giving `v / 2 - m` each.
Maynard Smith showed:
(i) no pure strategy is an ESS, since against a population playing `m` the mutant `m + ε` does
better; (ii) the mixed strategy `I` with density `(1/v) e^{-x/v}` on `[0, ∞)` (Mathlib's
`ProbabilityTheory.expMeasure` with rate `v⁻¹`) is an equilibrium:
every pure `m` earns `0` against it; (iii) `I` is stable against every pure mutant `J = m > 0`:
`I` earns more against `J` than `J` earns against itself.

Recorded here: clauses (i)–(iii). Uniqueness of the ESS among all mixed strategies (Bishop and
Cannings 1978) was read only in the abstract and is not formalized.

Sources: J. Maynard Smith, "The theory of games and the evolution of animal conflicts", J. Theor.
Biol. 47 (1974) 209–221, doi:10.1016/0022-5193(74)90110-6, §3; D. T. Bishop and C. Cannings, "A
generalized war of attrition", J. Theor. Biol. 70 (1978) 85–124,
doi:10.1016/0022-5193(78)90304-1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Exponential

@[expose] public section

namespace WantedExt.Biology.Ecology.WarOfAttritionWanted

open MeasureTheory

/-- **War of attrition payoff.** The payoff to a contestant prepared to pay `m` against one prepared
to pay `m'`, for a resource of value `v`: `v - m'` if `m > m'`, `-m` if `m < m'`, and `v / 2 - m` if
`m = m'`. -/
noncomputable def payoff (v m m' : ℝ) : ℝ :=
  if m' < m then v - m' else if m < m' then -m else v / 2 - m

/-- **Exponential persistence strategy.** The persistence strategy `I`: Mathlib's exponential law
`ProbabilityTheory.expMeasure` with rate `v⁻¹`. For `v > 0` it is a probability law
(`ProbabilityTheory.isProbabilityMeasure_expMeasure`) with density `(1/v) e^{-x/v}` for `x ≥ 0`
and `0` for `x < 0`, and mean `v`. -/
noncomputable def exponentialStrategy (v : ℝ) : Measure ℝ :=
  ProbabilityTheory.expMeasure v⁻¹

/-- **Payoff against a mixed strategy.** The expected payoff of the pure strategy `m` against the
mixed strategy `I`. -/
noncomputable def payoffAgainst (v m : ℝ) (μ : Measure ℝ) : ℝ := ∫ x, payoff v m x ∂μ

/-- **Payoff of a mixed strategy.** The expected payoff of the mixed strategy `I` against the pure
strategy `m`. -/
noncomputable def payoffOf (v : ℝ) (μ : Measure ℝ) (m : ℝ) : ℝ := ∫ x, payoff v x m ∂μ

/-- **No pure ESS.** Let `v > 0`. For every pure strategy `m ≥ 0` there
is a pure mutant `m' ≥ 0`, `m' ≠ m`, that earns strictly more against `m` than `m` earns against
itself: `E(m', m) > E(m, m)`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted no_pure_ess (v : ℝ) (hv : 0 < v) (m : ℝ) (hm : 0 ≤ m) :
    ∃ m' : ℝ, 0 ≤ m' ∧ m' ≠ m ∧ payoff v m m < payoff v m' m

/-- **The exponential strategy equalizes payoffs.** Let `v > 0`, so that the exponential law `I`
with rate `v⁻¹` (mean `v`) is a probability measure. Every pure strategy `m ≥ 0` earns exactly `0`
against it: `E(m, I) = 0`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted payoffAgainst_exponential (v : ℝ) (hv : 0 < v) :
    ∀ m : ℝ, 0 ≤ m → payoffAgainst v m (exponentialStrategy v) = 0

/-- **Stability against pure mutants.** Let `v > 0`. For every pure
mutant `m > 0`, the exponential strategy `I` earns more against `m` than `m` earns against
itself: `E(m, m) < E(I, m)`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted stable_against_pure (v : ℝ) (hv : 0 < v) (m : ℝ) (hm : 0 < m) :
    payoff v m m < payoffOf v (exponentialStrategy v) m

end WantedExt.Biology.Ecology.WarOfAttritionWanted
