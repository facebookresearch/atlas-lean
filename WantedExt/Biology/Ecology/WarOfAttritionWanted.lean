/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The war of attrition: no pure ESS, and the exponential persistence strategy

In Maynard Smith's war of attrition (1974, §3) each contestant chooses the cost `m ≥ 0` it is
prepared to pay, linear in display time. If `m₁ > m₂` the first gets `v - m₂` and the second
`-m₂`; equal choices split the resource, giving `v / 2 - m` each. Maynard Smith showed:
(i) no pure strategy is an ESS, since against a population playing `m` the mutant `m + ε` does
better; (ii) the mixed strategy `I` with density `(1/v) e^{-x/v}` on `[0, ∞)` is an equilibrium:
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
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

namespace WantedExt.Biology.Ecology.WarOfAttritionWanted

open MeasureTheory

/-- The payoff to a contestant prepared to pay `m` against one prepared to pay `m'`, for a
resource of value `v`: `v - m'` if `m > m'`, `-m` if `m < m'`, and `v / 2 - m` if `m = m'`. -/
noncomputable def payoff (v m m' : ℝ) : ℝ :=
  if m' < m then v - m' else if m < m' then -m else v / 2 - m

/-- The persistence strategy `I`: the exponential law on `[0, ∞)` with mean `v`, i.e. the measure
with density `(1/v) e^{-x/v}` for `x ≥ 0` and `0` for `x < 0` with respect to Lebesgue measure. -/
noncomputable def exponentialStrategy (v : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (if 0 ≤ x then v⁻¹ * Real.exp (-x / v) else 0)

/-- The expected payoff of the pure strategy `m` against the mixed strategy `I`. -/
noncomputable def payoffAgainst (v m : ℝ) (μ : Measure ℝ) : ℝ := ∫ x, payoff v m x ∂μ

/-- The expected payoff of the mixed strategy `I` against the pure strategy `m`. -/
noncomputable def payoffOf (v : ℝ) (μ : Measure ℝ) (m : ℝ) : ℝ := ∫ x, payoff v x m ∂μ

/-- **No pure ESS** (Maynard Smith 1974, §3): let `v > 0`. For every pure strategy `m ≥ 0` there
is a pure mutant `m' ≥ 0`, `m' ≠ m`, that earns strictly more against `m` than `m` earns against
itself: `E(m', m) > E(m, m)`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted no_pure_ess (v : ℝ) (hv : 0 < v) (m : ℝ) (hm : 0 ≤ m) :
    ∃ m' : ℝ, 0 ≤ m' ∧ m' ≠ m ∧ payoff v m m < payoff v m' m

/-- **The exponential strategy equalizes payoffs** (Maynard Smith 1974, §3): let `v > 0`. The
exponential law `I` with mean `v` is a probability measure, and every pure strategy `m ≥ 0`
earns exactly `0` against it: `E(m, I) = 0`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted payoffAgainst_exponential (v : ℝ) (hv : 0 < v) :
    IsProbabilityMeasure (exponentialStrategy v) ∧
      ∀ m : ℝ, 0 ≤ m → payoffAgainst v m (exponentialStrategy v) = 0

/-- **Stability against pure mutants** (Maynard Smith 1974, §3): let `v > 0`. For every pure
mutant `m > 0`, the exponential strategy `I` earns more against `m` than `m` earns against
itself: `E(m, m) < E(I, m)`.

Source: Maynard Smith (1974), §3. -/
public theorem_wanted stable_against_pure (v : ℝ) (hv : 0 < v) (m : ℝ) (hm : 0 < m) :
    payoff v m m < payoffOf v (exponentialStrategy v) m

end WantedExt.Biology.Ecology.WarOfAttritionWanted
