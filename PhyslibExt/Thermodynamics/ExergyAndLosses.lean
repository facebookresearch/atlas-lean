/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Analysis.Numerical.Certified
public import PhyslibExt.HeatTransfer.HeatExchangers
public import PhyslibExt.Thermodynamics.GasCycles
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exergy and losses: exergy destruction, nonideal Brayton losses, regeneration and property tables

## i. Overview

A steady open system exchanges heat `Q̇ⱼ` through ports `j` at boundary temperatures `Tⱼ`,
exchanges shaft power, and carries mass through inlet streams `i` and outlet streams `o`. The
first law and the entropy balance are separately declared model inputs with matched ports: each
stream enters both balances with the same mass flow `ṁ`, carrying energy `ṁ θ` and entropy
`ṁ s`, and each heat port enters both with the same heat rate, carrying energy `Q̇ⱼ` and entropy
`Q̇ⱼ / Tⱼ`. Here `θ = h + |v|² / 2 + g z` is the port energy per unit mass of
`ControlVolumes.portEnergyRate_eq_massFlow` (flow work counted once, inside `h`), and the shaft
work out is `ProcessPorts.workOut w` for the power `w` delivered to the system (IUPAC sign).
Heat rates are positive into the system; mass flows are positive along the flow, into the
system at an inlet and out of it at an outlet.

The entropy generation rate `Ṡ_gen = ∑ₒ ṁₒ sₒ - ∑ᵢ ṁᵢ sᵢ - ∑ⱼ Q̇ⱼ / Tⱼ` is the residual of the
steady entropy balance; it is not assumed nonnegative. The exergy destruction rate is the
residual of the steady exergy balance, exergy in minus exergy out,
`Ẋ_dest = ∑ⱼ (1 - T₀ / Tⱼ) Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ ψᵢ - ∑ₒ ṁₒ ψₒ`, with the flow exergy
`ψ = θ - h₀ - T₀ (s - s₀)` taken relative to one dead state `(T₀, h₀, s₀)` in every stream
term. The decomposition
`Ẋ_dest = (first-law residual) + (T₀ s₀ - h₀) (∑ ṁᵢ - ∑ ṁₒ) + T₀ Ṡ_gen` is algebra; with the
steady first law and the steady mass balance it is the Gouy-Stodola relation
`Ẋ_dest = T₀ Ṡ_gen`. Nonnegativity of `Ẋ_dest` follows only from the supplied second-law input
`Ṡ_gen ≥ 0`; energy conservation alone does not give it.

Model inputs and scope: the two balances are hypotheses, never derived. The stream exergy is
thermomechanical; chemical exergy is excluded (non-reacting streams, restricted dead state).
Temperatures are absolute; the physical case is `T₀ > 0` and `Tⱼ > 0`. The identities hold for
all real values, and each result assumes only the hypotheses its proof uses. The Carnot factor
`1 - T₀ / Tⱼ` is negative for a port colder than the environment, a physical case for exergy.

Nonideal Brayton cycle (section C). The ideal Brayton loop of `GasCycles` (its section D) runs per
unit mass of an ideal gas with specific gas constant `R > 0` and constant specific heat `cp > R` at
pressure ratio `rp > 1`, with `a = rp ^ (R / cp) > 1` (`GasCycles.braytonTempRatio`), between the
compressor inlet temperature `T₁ > 0` and the turbine inlet temperature `T₃`. Real compressors and
turbines are adiabatic but irreversible. Their isentropic efficiencies `ηc` and `ηt`, model inputs
in the physical range `(0, 1]`, compare the actual work with the isentropic work between the same
pressures: the compressor takes `cp (T₂ - T₁) = cp (T₂ₛ - T₁) / ηc` and the turbine gives
`cp (T₃ - T₄) = ηt cp (T₃ - T₄ₛ)`, where `T₂ₛ = a T₁` and `T₄ₛ = T₃ / a` are the ideal exits
`GasCycles.braytonCompressedTemp` and `GasCycles.braytonExpandedTemp`. So
`T₂ = T₁ + T₁ (a - 1) / ηc` and `T₄ = T₃ - ηt T₃ (1 - 1 / a)`. The heat legs stay isobaric; with
constant `cp` and fixed `rp`, `T₁` and `T₃`, the heat added is `Qin = cp (T₃ - T₂)`, the heat
rejected `Qout = cp (T₄ - T₁)`, and the net work output (engineering sign, as
`GasCycles.braytonNetWork`) is
`Wnet = cp (T₃ - T₄) - cp (T₂ - T₁) = Qin - Qout = cp (1 - 1 / a) (ηt T₃ - a T₁ / ηc)`.

Losses carry one sign: on the physical ranges they raise both exit temperatures, `T₂ₛ ≤ T₂` and
`T₄ₛ ≤ T₄`, so the extra compressor work `cp (T₂ - T₂ₛ)` and the turbine work deficit
`cp (T₄ - T₄ₛ)` are nonnegative. The net work is positive exactly when `ηc ηt > a T₁ / T₃` and
zero exactly at equality; the back-work ratio, compressor input over turbine output, is
`a T₁ / (ηc ηt T₃)`. The work rises strictly with each efficiency.

The work-to-heat ratio `Wnet / Qin` (`braytonLossyEfficiency`) is defined for all real inputs, but
it is the thermal efficiency only for positive heat input `Qin > 0`, that is `T₃ > T₂`, and every
efficiency statement here assumes it. On positive heat input the efficiency rises strictly with
each component efficiency and is at most the ideal `1 - 1 / a` (`GasCycles.braytonEfficiency`),
with equality exactly at `ηc = ηt = 1`, where every quantity of the loop is the ideal one of
`GasCycles`. For `Qin < 0` the ratio is no efficiency and can fall as `ηt` rises (see the tests),
and at `Qin = 0` Lean's value `0` of the ratio is meaningless.

Model inputs and scope of section C: the efficiencies are given constants, not derived from flow
physics; the gas is cold-air standard (constant `cp`); the heat exchangers have no pressure loss
and there is no regeneration. No empirical adequacy or vehicle or system safety claim.

Regeneration (section D). A regenerator preheats the compressed stream of the nonideal loop with
the turbine exhaust before the combustor. It is the counterflow exchanger of
`HeatTransfer.HeatExchangers` with the exhaust as the hot stream, entering at `T₄`, and the
compressed stream as the cold stream, entering at `T₂`. Both carry the cycle's mass flow `ṁ` at
the same `cp`, so both capacity rates are `ṁ cp`: per unit mass flow both are `cp`, the
capacity-rate ratio is `Cr = 1`, `UA` is the conductance per unit mass flow and `NTU = UA / cp`.
The effectiveness is the equal-capacity branch `ε = NTU / (1 + NTU) = UA / (cp + UA)` of
`HeatTransfer.HeatExchangers.counterflowEffectiveness`, with `0 ≤ ε < 1`; the general formula's
`0 / 0` never enters.

Heat flows from the exhaust into the compressed stream only if the exhaust is hotter, so the
regenerator ports are defined by cases. When `T₂ < T₄`, the compressed stream leaves the
regenerator at `T₅ = T₂ + ε (T₄ - T₂)` and the exhaust at `T₆ = T₄ - ε (T₄ - T₂)`, and the
recovered heat is the effectiveness contract `Q_reg = ε Cmin (T₄ - T₂)` with `Cmin = cp`; every
counterflow solution between the ports has exactly these outlets. When `T₄ ≤ T₂`, equality
included, the regenerator is bypassed: `T₅ = T₂`, `T₆ = T₄` and `Q_reg = 0`. Connected against
the gradient, `T₄ < T₂`, an exchanger with `UA > 0` would reverse the heat flow, cooling the
compressed stream and heating the exhaust.

On both branches the heat lost by the exhaust equals the heat gained by the compressed stream,
`cp (T₄ - T₆) = cp (T₅ - T₂) = Q_reg`; the external heat demand `Qin_reg = cp (T₃ - T₅)` is `Qin`
less `Q_reg`; and the net work is unchanged, `Wnet = Qin_reg - cp (T₆ - T₁)`. For `cp > 0` and
`UA ≥ 0` the recovered heat is never negative and is positive exactly when `T₂ < T₄` and
`UA > 0`, so the external heat demand falls exactly then; on the physical ranges it stays
positive when the loop without regenerator has positive heat input. No efficiency benefit is
asserted for a backward temperature gradient: in the bypass the work-to-heat ratio is that of
section C. Model inputs and scope of section D: the counterflow model of `HeatExchangers`
(constant capacity rates and conductance, no phase change, axial conduction, pressure loss or
heat leak) on the loop of section C.

Property tables (section E). The port enthalpies can also come from a supplied property table
instead of the cold-air model `h = cp T`. A `PropertyTable` lists nodes `(Tₖ, hₖ)` as exact
rationals (K, J/kg) with strictly increasing positive temperatures and carries a supplied
interpolation-error envelope, written `ε ≥ 0` in section E (it is not the regenerator
effectiveness of section D). At an in-range temperature the table interpolates linearly between
the bracketing nodes, and `PropertyTable.lookup` returns the rational interval `[q - ε, q + ε]`
(`RatInterval` of `MathlibExt.Analysis.Numerical.Certified`) around the interpolant `q`; outside
the table range it returns no value, so nothing is extrapolated. The declared property model is
any `h` within `ε` of the interpolant wherever the table interpolates
(`PropertyTable.WithinEnvelope`), a model input to be justified for the chosen model; no theorem
derives it or infers or certifies the tabulated data. Under it every certified port value
encloses `h`, and interval differences enclose the heat added `h(T₃) - h(T₂)`, the heat rejected
`h(T₄) - h(T₁)` and the net work `(h(T₃) - h(T₄)) - (h(T₂) - h(T₁))` of the declared model.

The enclosures carry the property error alone: each port interval has width `2 ε`, the heat
enclosures `4 ε` and the work enclosure `8 ε`. The port temperatures are exact inputs, so no
solver error enters, and the conclusions concern the declared model, not the physical fluid; a
separately declared solver error and physical-model error widen an enclosure only through their
own bounds. For the cold-air model at the section C port states the enclosures contain the heats
and the net work of section C. No empirical adequacy or vehicle or system safety claim.

## ii. Key results

- `ExergyAndLosses.exergyDestroyed_eq_add`: the decomposition of `Ẋ_dest` for every dead state.
- `ExergyAndLosses.exergyDestroyed_eq_mul_entropyGen`: `Ẋ_dest = T₀ Ṡ_gen` under the steady
  first law and mass balance.
- `ExergyAndLosses.exergyDestroyed_nonneg`: `0 ≤ Ẋ_dest` from the supplied `0 ≤ Ṡ_gen`.
- `ExergyAndLosses.exergyDestroyed_sub_ref`, `ExergyAndLosses.exergyDestroyed_ref_eq`: a change
  of dead state moves `Ẋ_dest` by a multiple of the mass imbalance, so not at all in steady flow.
- `ExergyAndLosses.braytonLossy_one`: at `ηc = ηt = 1` the nonideal Brayton loop is the ideal one.
- `ExergyAndLosses.braytonLossy_isentropicEfficiency`: the states realize the isentropic
  efficiencies `ηc = (T₂ₛ - T₁) / (T₂ - T₁)` and `ηt = (T₃ - T₄) / (T₃ - T₄ₛ)`.
- `ExergyAndLosses.braytonLossy_temp_order`: `T₁ < T₂ₛ ≤ T₂` and `T₄ₛ ≤ T₄ < T₃`.
- `ExergyAndLosses.braytonLossy_closed_loop`:
  `Wnet = Qin - Qout = cp (1 - 1 / a) (ηt T₃ - a T₁ / ηc)`.
- `ExergyAndLosses.braytonLossyEfficiency_eq`: on positive heat input, `η = 1 - Qout / Qin` and
  its closed form.
- `ExergyAndLosses.braytonLossy_backWorkRatio`: the back-work ratio `a T₁ / (ηc ηt T₃)`.
- `ExergyAndLosses.braytonLossyNetWork_pos_iff`, `ExergyAndLosses.braytonLossyNetWork_eq_zero_iff`:
  positive work exactly when `ηc ηt > a T₁ / T₃`, zero work exactly at equality.
- `ExergyAndLosses.braytonLossyNetWork_strictMonoOn_compressorEff`,
  `ExergyAndLosses.braytonLossyNetWork_strictMonoOn_turbineEff`: the work rises with each
  efficiency on `(0, 1]`.
- `ExergyAndLosses.braytonLossyEfficiency_strictMonoOn_compressorEff`,
  `ExergyAndLosses.braytonLossyEfficiency_strictMonoOn_turbineEff`: on positive heat input the
  efficiency rises with each component efficiency.
- `ExergyAndLosses.braytonLossyEfficiency_le_braytonEfficiency`: on positive heat input
  `η ≤ 1 - 1 / a`, with equality exactly at `ηc = ηt = 1`.
- `ExergyAndLosses.braytonRegen_effectiveness`: the regenerator has `Cr = 1`, `NTU = UA / cp` and
  `ε = UA / (cp + UA) ∈ [0, 1)`.
- `ExergyAndLosses.braytonRegen_of_lt`, `ExergyAndLosses.braytonRegen_bypass`: the ports when the
  exhaust is hotter, and the bypass otherwise, with the work-to-heat ratio of section C.
- `ExergyAndLosses.braytonRegen_heat_balance`: `cp (T₄ - T₆) = Q_reg`, `Qin_reg = Qin - Q_reg` and
  `Wnet = Qin_reg - cp (T₆ - T₁)`.
- `ExergyAndLosses.braytonRegenHeat_nonneg`, `ExergyAndLosses.braytonRegenHeat_pos_iff`: no
  negative recovery; positive recovery exactly for `T₂ < T₄` and `UA > 0`.
- `ExergyAndLosses.braytonRegenHeatIn_le_braytonLossyHeatIn`,
  `ExergyAndLosses.braytonRegenHeatIn_pos`: the external heat demand falls exactly then and stays
  positive.
- `ExergyAndLosses.braytonRegen_temp_order`: `T₂ ≤ T₅ < T₄` and `T₂ < T₆ ≤ T₄` when `T₂ < T₄`.
- `ExergyAndLosses.braytonRegen_of_isCounterflowSolution`,
  `ExergyAndLosses.braytonRegen_reversal_of_isCounterflowSolution`: every counterflow solution
  between the ports realizes `T₅` and `T₆`; connected against the gradient it would reverse the
  heat flow.
- `ExergyAndLosses.PropertyTable.lookup_encloses`: under the envelope a certified port value
  encloses the declared property model.
- `ExergyAndLosses.PropertyTable.lookup_eq_none_iff`: no certified value exactly outside the
  table range.
- `ExergyAndLosses.PropertyTable.width_of_lookup_eq_some`,
  `ExergyAndLosses.PropertyTable.InRange.pos`: each port interval has width `2 ε`; in-range
  temperatures are positive.
- `ExergyAndLosses.PropertyTable.heatInEnclosure_encloses`,
  `ExergyAndLosses.PropertyTable.heatOutEnclosure_encloses`,
  `ExergyAndLosses.PropertyTable.netWorkEnclosure_encloses`: the composed heat and work enclosures
  include the declared model, with widths `4 ε`, `4 ε` and `8 ε`.
- `ExergyAndLosses.PropertyTable.portEnclosures_eq_none_iff`: no composed value when a port
  temperature is outside the table.
- `ExergyAndLosses.encloses_sub_ofCenter_of_errors`: solver and physical-model errors enter as
  separate declared bounds.
- `ExergyAndLosses.braytonLossy_encloses`: for the cold-air model at the section C ports the
  enclosures contain the section C heats and net work.

## iii. Table of contents

- A. Balances with matched ports
- B. Exergy destruction
- C. Nonideal Brayton cycle
  - C.1. States
  - C.2. Work and heat
  - C.3. The positive-work threshold
  - C.4. Monotonicity in the component efficiencies
- D. Regeneration without heat-flow reversal
  - D.1. Regenerator ports
  - D.2. No heat-flow reversal
  - D.3. The counterflow exchanger between the ports
- E. Property-table enclosure at the cycle port
  - E.1. Tables, lookups and the supplied envelope
  - E.2. Port enclosures
  - E.3. Property error kept apart

## iv. References

- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill,
  ch. 7-8: the entropy balance with entropy generation, flow exergy
  `ψ = (h - h₀) - T₀ (s - s₀) + V² / 2 + g z`, exergy of heat `(1 - T₀ / T) Q`, the exergy
  balance and `X_destroyed = T₀ S_gen`.
- A. Bejan, *Advanced Engineering Thermodynamics*, Wiley, ch. 3: the Gouy-Stodola theorem.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 7:
  isentropic efficiencies of adiabatic turbines and compressors,
  `η_T = (h₃ - h₄ₐ) / (h₃ - h₄ₛ)` and `η_C = (h₂ₛ - h₁) / (h₂ₐ - h₁)`, temperature ratios for
  constant specific heats.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the Brayton cycle, deviation of actual gas-turbine cycles from idealized ones, and the back
  work ratio `r_bw = w_comp,in / w_turb,out`.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 9:
  the Brayton cycle with regeneration, `q_regen = h₅ - h₂`, the regenerator effectiveness
  `ε = (h₅ - h₂) / (h₄ - h₂)`, and regeneration only when the turbine exhaust is hotter than the
  compressed air, since otherwise heat flows the other way.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, 6th ed., Wiley (2007), Section 11.4: `q = ε Cmin (Th,i - Tc,i)` and the counterflow
  effectiveness `ε = NTU / (1 + NTU)` at `Cr = 1`.
- R. L. Burden and J. D. Faires, *Numerical Analysis*, 10th ed., Cengage Learning, 2016, ch. 3:
  linear and piecewise-linear interpolation and the interpolation error.
- W. Tucker, *Validated Numerics: A Short Introduction to Rigorous Computations*, Princeton
  University Press, 2011: interval enclosures and interval arithmetic.
- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill, ch. 3
  and 7: property tables with linear interpolation, and ideal-gas enthalpy tables of air.
-/

@[expose] public section

namespace ExergyAndLosses

variable {σ ι κ : Type*} [Fintype σ] [Fintype ι] [Fintype κ]

/-! ## A. Balances with matched ports -/

/-- Residual of the steady first law of an open system: heat in, minus shaft work out, plus the
energy carried in by the inlet streams, minus that carried out by the outlet streams,
`∑ⱼ Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ θᵢ - ∑ₒ ṁₒ θₒ`, with `Ẇ_out = ProcessPorts.workOut w` for the power `w`
delivered to the system and `θ = h + |v|² / 2 + g z` the port energy per unit mass. The
declared steady first law is `energyResidual Q w mi θi mo θo = 0`. -/
def energyResidual (Q : σ → ℝ) (w : ℝ) (mi θi : ι → ℝ) (mo θo : κ → ℝ) : ℝ :=
  ∑ j, Q j - ProcessPorts.workOut w + ∑ i, mi i * θi i - ∑ o, mo o * θo o

/-- Entropy generation rate as the residual of the steady entropy balance with the same ports:
`Ṡ_gen = ∑ₒ ṁₒ sₒ - ∑ᵢ ṁᵢ sᵢ - ∑ⱼ Q̇ⱼ / Tⱼ`. It is a balance residual, not automatically
nonnegative; the second law is the separate input `0 ≤ Ṡ_gen`. Physical boundary temperatures
are positive; at `Tⱼ = 0` Lean's `x / 0 = 0` gives a meaningless term. -/
noncomputable def entropyGen (Q Tb : σ → ℝ) (mi si : ι → ℝ) (mo so : κ → ℝ) : ℝ :=
  ∑ o, mo o * so o - ∑ i, mi i * si i - ∑ j, Q j / Tb j

/-- Specific flow exergy of a stream with port energy `θ = h + |v|² / 2 + g z` and specific
entropy `s`, relative to the dead state at temperature `T₀` with enthalpy `h₀` and entropy `s₀`:
`ψ = θ - h₀ - T₀ (s - s₀) = (h - h₀) - T₀ (s - s₀) + |v|² / 2 + g z`. Thermomechanical part only;
chemical exergy is excluded. -/
def flowExergy (T0 h0 s0 θ s : ℝ) : ℝ := θ - h0 - T0 * (s - s0)

/-! ## B. Exergy destruction -/

/-- Exergy destruction rate as the residual of the steady exergy balance, exergy in minus exergy
out: `Ẋ_dest = ∑ⱼ (1 - T₀ / Tⱼ) Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ ψᵢ - ∑ₒ ṁₒ ψₒ`, with one dead state
`(T₀, h₀, s₀)` in every stream term. -/
noncomputable def exergyDestroyed (T0 h0 s0 : ℝ) (Q Tb : σ → ℝ) (w : ℝ) (mi θi si : ι → ℝ)
    (mo θo so : κ → ℝ) : ℝ :=
  ∑ j, (1 - T0 / Tb j) * Q j - ProcessPorts.workOut w +
    ∑ i, mi i * flowExergy T0 h0 s0 (θi i) (si i) - ∑ o, mo o * flowExergy T0 h0 s0 (θo o) (so o)

/-- **Exergy destruction decomposed.** For every dead state `(T₀, h₀, s₀)`, the destruction rate
is the first-law residual, plus the dead-state terms times the mass imbalance, plus `T₀` times
the entropy generation:
`Ẋ_dest = (first-law residual) + (T₀ s₀ - h₀) (∑ ṁᵢ - ∑ ṁₒ) + T₀ Ṡ_gen`. -/
lemma exergyDestroyed_eq_add (T0 h0 s0 : ℝ) (Q Tb : σ → ℝ) (w : ℝ) (mi θi si : ι → ℝ)
    (mo θo so : κ → ℝ) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so =
      energyResidual Q w mi θi mo θo + (T0 * s0 - h0) * (∑ i, mi i - ∑ o, mo o) +
        T0 * entropyGen Q Tb mi si mo so := by
  unfold exergyDestroyed energyResidual entropyGen flowExergy
  have hQ : ∑ j, (1 - T0 / Tb j) * Q j = ∑ j, Q j - T0 * ∑ j, Q j / Tb j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi : ∑ i, mi i * (θi i - h0 - T0 * (si i - s0))
      = ∑ i, mi i * θi i + (T0 * s0 - h0) * ∑ i, mi i - T0 * ∑ i, mi i * si i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ho : ∑ o, mo o * (θo o - h0 - T0 * (so o - s0))
      = ∑ o, mo o * θo o + (T0 * s0 - h0) * ∑ o, mo o - T0 * ∑ o, mo o * so o := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [hQ, hi, ho]
  ring

/-- **Gouy-Stodola relation.** Under the declared steady first law and the steady mass balance
`∑ ṁᵢ = ∑ ṁₒ`, the destroyed exergy is `Ẋ_dest = T₀ Ṡ_gen`, for every dead state. -/
lemma exergyDestroyed_eq_mul_entropyGen {T0 h0 s0 w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (henergy : energyResidual Q w mi θi mo θo = 0)
    (hmass : ∑ i, mi i = ∑ o, mo o) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so = T0 * entropyGen Q Tb mi si mo so := by
  rw [exergyDestroyed_eq_add, henergy, hmass]
  ring

/-- **Nonnegative destruction from the supplied second law.** With the environment at
`T₀ > 0`, the steady first law, the steady mass balance and the second-law input `0 ≤ Ṡ_gen`,
the destroyed exergy is nonnegative. Without `0 ≤ Ṡ_gen` the conclusion can fail
(`fixture_energy_without_second_law`). -/
lemma exergyDestroyed_nonneg {T0 h0 s0 w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (hT0 : 0 < T0) (henergy : energyResidual Q w mi θi mo θo = 0)
    (hmass : ∑ i, mi i = ∑ o, mo o) (hgen : 0 ≤ entropyGen Q Tb mi si mo so) :
    0 ≤ exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so := by
  rw [exergyDestroyed_eq_mul_entropyGen henergy hmass]
  exact mul_nonneg (le_of_lt hT0) hgen

/-- **Change of dead state.** Replacing the dead-state enthalpy and entropy `(h₀, s₀)` by
`(h₀', s₀')` in every stream term changes the destroyed exergy by
`(h₀' - h₀ - T₀ (s₀' - s₀)) (∑ ṁᵢ - ∑ ṁₒ)`. -/
lemma exergyDestroyed_sub_ref (T0 h0 s0 h0' s0' : ℝ) (Q Tb : σ → ℝ) (w : ℝ)
    (mi θi si : ι → ℝ) (mo θo so : κ → ℝ) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so -
        exergyDestroyed T0 h0' s0' Q Tb w mi θi si mo θo so =
      (h0' - h0 - T0 * (s0' - s0)) * (∑ i, mi i - ∑ o, mo o) := by
  unfold exergyDestroyed flowExergy
  have hi : ∑ i, mi i * (θi i - h0 - T0 * (si i - s0))
      = ∑ i, mi i * (θi i - h0' - T0 * (si i - s0')) +
        (h0' - h0 - T0 * (s0' - s0)) * ∑ i, mi i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ho : ∑ o, mo o * (θo o - h0 - T0 * (so o - s0))
      = ∑ o, mo o * (θo o - h0' - T0 * (so o - s0')) +
        (h0' - h0 - T0 * (s0' - s0)) * ∑ o, mo o := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [hi, ho]
  ring

/-- In steady flow (`∑ ṁᵢ = ∑ ṁₒ`) the destroyed exergy does not depend on the dead-state
enthalpy and entropy, provided the same dead state is used in every stream term. -/
lemma exergyDestroyed_ref_eq {T0 h0 s0 h0' s0' w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (hmass : ∑ i, mi i = ∑ o, mo o) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so =
      exergyDestroyed T0 h0' s0' Q Tb w mi θi si mo θo so := by
  have h := exergyDestroyed_sub_ref T0 h0 s0 h0' s0' Q Tb w mi θi si mo θo so
  rw [hmass, sub_self, mul_zero] at h
  exact sub_eq_zero.mp h

/-! ## C. Nonideal Brayton cycle -/

open GasCycles

/-! ### C.1. States -/

/-- Compressor exit temperature `T₂ = T₁ + T₁ (a - 1) / ηc`, `a = rp ^ (R / cp)`, of the adiabatic
compression from `(p₁, T₁)` to `rp p₁` with isentropic efficiency `ηc`: the work input is the
isentropic one, `cp (a T₁ - T₁)`, divided by `ηc`. Physical domain `0 < ηc ≤ 1` with `rp > 1`,
`cp > R > 0` and `T₁ > 0`. -/
noncomputable def braytonLossyCompressedTemp (T₁ rp R cp ηc : ℝ) : ℝ :=
  T₁ + T₁ * (braytonTempRatio rp R cp - 1) / ηc

/-- Turbine exit temperature `T₄ = T₃ - ηt T₃ (1 - 1 / a)` of the adiabatic expansion from
`(rp p₁, T₃)` back to `p₁` with isentropic efficiency `ηt`: the work output is the isentropic one,
`cp (T₃ - T₃ / a)`, times `ηt`. Physical domain `0 < ηt ≤ 1` with `rp > 1`, `cp > R > 0` and
`T₃ > 0`. -/
noncomputable def braytonLossyExpandedTemp (T₃ rp R cp ηt : ℝ) : ℝ :=
  T₃ - ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp)

/-- Heat added per unit mass on the isobaric leg `2 → 3` of the nonideal loop,
`Qin = cp (T₃ - T₂)`, with the nonideal compressor exit `T₂`. -/
noncomputable def braytonLossyHeatIn (T₁ T₃ rp R cp ηc : ℝ) : ℝ :=
  cp * (T₃ - braytonLossyCompressedTemp T₁ rp R cp ηc)

/-- Heat rejected per unit mass on the closing isobaric leg `4 → 1` of the nonideal loop,
`Qout = cp (T₄ - T₁)`, with the nonideal turbine exit `T₄`. -/
noncomputable def braytonLossyHeatOut (T₁ T₃ rp R cp ηt : ℝ) : ℝ :=
  cp * (braytonLossyExpandedTemp T₃ rp R cp ηt - T₁)

/-- Net work output per unit mass of the nonideal loop (engineering sign): the turbine output
`cp (T₃ - T₄)` minus the compressor input `cp (T₂ - T₁)`. -/
noncomputable def braytonLossyNetWork (T₁ T₃ rp R cp ηc ηt : ℝ) : ℝ :=
  cp * (T₃ - braytonLossyExpandedTemp T₃ rp R cp ηt) -
    cp * (braytonLossyCompressedTemp T₁ rp R cp ηc - T₁)

/-- Thermal efficiency of the nonideal loop, the work-to-heat ratio `η = Wnet / Qin`. It is
meaningful only for positive heat input `Qin > 0`; at `Qin = 0` Lean's value `0` is meaningless. -/
noncomputable def braytonLossyEfficiency (T₁ T₃ rp R cp ηc ηt : ℝ) : ℝ :=
  braytonLossyNetWork T₁ T₃ rp R cp ηc ηt / braytonLossyHeatIn T₁ T₃ rp R cp ηc

/-- `a = rp ^ (R / cp) > 1` on the physical domain. -/
private lemma one_lt_braytonTempRatio {cp R rp : ℝ} (hR : 0 < R) (hRcp : R < cp) (hrp : 1 < rp) :
    1 < braytonTempRatio rp R cp := by
  simp only [braytonTempRatio]
  exact Real.one_lt_rpow hrp (div_pos hR (lt_trans hR hRcp))

/-- The threshold factorization `Wnet = cp (1 - 1 / a) (T₃ / ηc) (ηc ηt - a T₁ / T₃)`. -/
private lemma braytonLossyNetWork_eq_mul {cp R rp T₁ T₃ ηc ηt : ℝ} (hrp : 0 < rp) (hηc : ηc ≠ 0)
    (hT₃ : T₃ ≠ 0) :
    braytonLossyNetWork T₁ T₃ rp R cp ηc ηt =
      cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ / ηc) *
        (ηc * ηt - braytonTempRatio rp R cp * T₁ / T₃) := by
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  simp only [braytonLossyNetWork, braytonLossyCompressedTemp, braytonLossyExpandedTemp]
  field_simp
  ring

/-- The nonideal compressor exit is above the inlet, hence positive. -/
private lemma braytonLossyCompressedTemp_pos {cp R rp T₁ ηc : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₁ : 0 < T₁) (hηc : 0 < ηc) :
    0 < braytonLossyCompressedTemp T₁ rp R cp ηc := by
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have h : 0 < T₁ * (braytonTempRatio rp R cp - 1) / ηc :=
    div_pos (mul_pos hT₁ (sub_pos.mpr ha1)) hηc
  simp only [braytonLossyCompressedTemp]
  linarith

/-- **Recovery of the ideal loop at efficiency one.** For all real parameters, at `ηc = ηt = 1`
the nonideal exit temperatures, heats, net work and work-to-heat ratio are the ideal ones of
`GasCycles`. -/
lemma braytonLossy_one (T₁ T₃ rp R cp : ℝ) :
    braytonLossyCompressedTemp T₁ rp R cp 1 = braytonCompressedTemp T₁ rp R cp ∧
      braytonLossyExpandedTemp T₃ rp R cp 1 = braytonExpandedTemp T₃ rp R cp ∧
      braytonLossyHeatIn T₁ T₃ rp R cp 1 = braytonHeatIn T₁ T₃ rp R cp ∧
      braytonLossyHeatOut T₁ T₃ rp R cp 1 = braytonHeatOut T₁ T₃ rp R cp ∧
      braytonLossyNetWork T₁ T₃ rp R cp 1 1 = braytonNetWork T₁ T₃ rp R cp ∧
      braytonLossyEfficiency T₁ T₃ rp R cp 1 1 =
        braytonNetWork T₁ T₃ rp R cp / braytonHeatIn T₁ T₃ rp R cp := by
  have h₂ : braytonLossyCompressedTemp T₁ rp R cp 1 = braytonCompressedTemp T₁ rp R cp := by
    simp only [braytonLossyCompressedTemp, braytonCompressedTemp]
    ring
  have h₄ : braytonLossyExpandedTemp T₃ rp R cp 1 = braytonExpandedTemp T₃ rp R cp := by
    simp only [braytonLossyExpandedTemp, braytonExpandedTemp]
    ring
  have hQin : braytonLossyHeatIn T₁ T₃ rp R cp 1 = braytonHeatIn T₁ T₃ rp R cp := by
    simp only [braytonLossyHeatIn, braytonHeatIn, h₂]
  have hQout : braytonLossyHeatOut T₁ T₃ rp R cp 1 = braytonHeatOut T₁ T₃ rp R cp := by
    simp only [braytonLossyHeatOut, braytonHeatOut, h₄]
  have hW : braytonLossyNetWork T₁ T₃ rp R cp 1 1 = braytonNetWork T₁ T₃ rp R cp := by
    simp only [braytonLossyNetWork, braytonNetWork, h₂, h₄]
  refine ⟨h₂, h₄, hQin, hQout, hW, ?_⟩
  rw [braytonLossyEfficiency, hW, hQin]

/-- The nonideal states realize the isentropic efficiencies: for `0 < R < cp`, `rp > 1`, `T₁ > 0`,
`T₃ > 0` and `ηc > 0`, the compressor efficiency is the isentropic over the actual temperature
rise, `ηc = (T₂ₛ - T₁) / (T₂ - T₁)`, and for every real `ηt` the turbine efficiency is the actual
over the isentropic temperature drop, `ηt = (T₃ - T₄) / (T₃ - T₄ₛ)`, with the ideal exits
`T₂ₛ = a T₁` and `T₄ₛ = T₃ / a` of `GasCycles`. -/
lemma braytonLossy_isentropicEfficiency {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₁ : 0 < T₁) (hT₃ : 0 < T₃) (hηc : 0 < ηc) :
    ηc = (braytonCompressedTemp T₁ rp R cp - T₁) /
        (braytonLossyCompressedTemp T₁ rp R cp ηc - T₁) ∧
      ηt = (T₃ - braytonLossyExpandedTemp T₃ rp R cp ηt) /
        (T₃ - braytonExpandedTemp T₃ rp R cp) := by
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hsub : braytonTempRatio rp R cp - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ha1)
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hηc0 : ηc ≠ 0 := ne_of_gt hηc
  constructor
  · simp only [braytonCompressedTemp, braytonLossyCompressedTemp]
    have hden : T₁ + T₁ * (braytonTempRatio rp R cp - 1) / ηc - T₁ =
        T₁ * (braytonTempRatio rp R cp - 1) / ηc := by ring
    rw [hden, eq_div_iff (div_ne_zero (mul_ne_zero (ne_of_gt hT₁) hsub) hηc0)]
    field_simp
  · simp only [braytonExpandedTemp, braytonLossyExpandedTemp]
    have hnum : T₃ - (T₃ - ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp)) =
        ηt * (T₃ * (1 - 1 / braytonTempRatio rp R cp)) := by ring
    have hden : T₃ - T₃ / braytonTempRatio rp R cp =
        T₃ * (1 - 1 / braytonTempRatio rp R cp) := by ring
    rw [hnum, hden, mul_div_assoc, div_self (mul_ne_zero (ne_of_gt hT₃) (ne_of_gt hc)),
      mul_one]

/-- Losses raise both exit temperatures: for `0 < R < cp`, `rp > 1`, `T₁ > 0`, `T₃ > 0`,
`0 < ηc ≤ 1` and `0 < ηt ≤ 1`, the compressor still heats and the turbine still cools, with
`T₁ < T₂ₛ ≤ T₂` and `T₄ₛ ≤ T₄ < T₃`. These are the loss signs: the extra compressor work
`cp (T₂ - T₂ₛ)` and the turbine work deficit `cp (T₄ - T₄ₛ)` are `cp > 0` times the nonnegative
differences. -/
lemma braytonLossy_temp_order {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₁ : 0 < T₁) (hT₃ : 0 < T₃) (hηc : 0 < ηc) (hηc₁ : ηc ≤ 1) (hηt : 0 < ηt)
    (hηt₁ : ηt ≤ 1) :
    T₁ < braytonCompressedTemp T₁ rp R cp ∧
      braytonCompressedTemp T₁ rp R cp ≤ braytonLossyCompressedTemp T₁ rp R cp ηc ∧
      braytonExpandedTemp T₃ rp R cp ≤ braytonLossyExpandedTemp T₃ rp R cp ηt ∧
      braytonLossyExpandedTemp T₃ rp R cp ηt < T₃ := by
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hb : 0 < T₁ * (braytonTempRatio rp R cp - 1) := mul_pos hT₁ (sub_pos.mpr ha1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [braytonCompressedTemp]
    nlinarith
  · simp only [braytonCompressedTemp, braytonLossyCompressedTemp]
    have h : T₁ * (braytonTempRatio rp R cp - 1) ≤ T₁ * (braytonTempRatio rp R cp - 1) / ηc := by
      rw [le_div_iff₀ hηc]
      nlinarith
    linarith
  · simp only [braytonExpandedTemp, braytonLossyExpandedTemp]
    have hTc : 0 < T₃ * (1 - 1 / braytonTempRatio rp R cp) := mul_pos hT₃ hc
    have h1 : T₃ / braytonTempRatio rp R cp = T₃ - T₃ * (1 - 1 / braytonTempRatio rp R cp) := by
      ring
    have h2 : ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp) ≤
        T₃ * (1 - 1 / braytonTempRatio rp R cp) := by nlinarith
    linarith
  · simp only [braytonLossyExpandedTemp]
    have h : 0 < ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp) := mul_pos (mul_pos hηt hT₃) hc
    linarith

/-! ### C.2. Work and heat -/

/-- First law around the nonideal loop and the work in closed form: for `rp > 0` the net work is
the net heat, `Wnet = Qin - Qout`, and `Wnet = cp (1 - 1 / a) (ηt T₃ - a T₁ / ηc)`, the turbine
output `cp ηt T₃ (1 - 1 / a)` minus the compressor input `cp T₁ (a - 1) / ηc`. -/
lemma braytonLossy_closed_loop {cp R rp T₁ T₃ ηc ηt : ℝ} (hrp : 0 < rp) :
    braytonLossyNetWork T₁ T₃ rp R cp ηc ηt =
        braytonLossyHeatIn T₁ T₃ rp R cp ηc - braytonLossyHeatOut T₁ T₃ rp R cp ηt ∧
      braytonLossyNetWork T₁ T₃ rp R cp ηc ηt =
        cp * (1 - 1 / braytonTempRatio rp R cp) *
          (ηt * T₃ - braytonTempRatio rp R cp * T₁ / ηc) := by
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hca : (1 - 1 / braytonTempRatio rp R cp) * braytonTempRatio rp R cp =
      braytonTempRatio rp R cp - 1 := by
    field_simp
  constructor
  · simp only [braytonLossyNetWork, braytonLossyHeatIn, braytonLossyHeatOut]
    ring
  · simp only [braytonLossyNetWork, braytonLossyCompressedTemp, braytonLossyExpandedTemp]
    linear_combination (cp * T₁ / ηc) * hca

/-- Work-to-heat ratios on positive heat input: for `0 < R < cp`, `rp > 0`, `ηc > 0` and
`T₃ > T₂`, the thermal efficiency is `η = 1 - Qout / Qin` and
`η = (1 - 1 / a) (ηc ηt T₃ - a T₁) / (ηc (T₃ - T₁) - (a - 1) T₁)`, whose denominator is
`ηc (T₃ - T₂) > 0`. -/
lemma braytonLossyEfficiency_eq {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 0 < rp) (hηc : 0 < ηc) (hT₃ : braytonLossyCompressedTemp T₁ rp R cp ηc < T₃) :
    braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt =
        1 - braytonLossyHeatOut T₁ T₃ rp R cp ηt / braytonLossyHeatIn T₁ T₃ rp R cp ηc ∧
      braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt =
        (1 - 1 / braytonTempRatio rp R cp) * (ηc * ηt * T₃ - braytonTempRatio rp R cp * T₁) /
          (ηc * (T₃ - T₁) - (braytonTempRatio rp R cp - 1) * T₁) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha : 0 < braytonTempRatio rp R cp := by
    simp only [braytonTempRatio]
    exact Real.rpow_pos_of_pos hrp _
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hηc0 : ηc ≠ 0 := ne_of_gt hηc
  have hQ : 0 < braytonLossyHeatIn T₁ T₃ rp R cp ηc := by
    simp only [braytonLossyHeatIn]
    exact mul_pos hcp (sub_pos.mpr hT₃)
  have hloop := braytonLossy_closed_loop (cp := cp) (R := R) (T₁ := T₁) (T₃ := T₃) (ηc := ηc)
    (ηt := ηt) hrp
  constructor
  · rw [braytonLossyEfficiency, hloop.1, sub_div, div_self (ne_of_gt hQ)]
  · have hD : 0 < ηc * (T₃ - T₁) - (braytonTempRatio rp R cp - 1) * T₁ := by
      have h : ηc * (T₃ - T₁) - (braytonTempRatio rp R cp - 1) * T₁ =
          ηc * (T₃ - braytonLossyCompressedTemp T₁ rp R cp ηc) := by
        simp only [braytonLossyCompressedTemp]
        field_simp
        ring
      rw [h]
      exact mul_pos hηc (sub_pos.mpr hT₃)
    rw [braytonLossyEfficiency, hloop.2, div_eq_div_iff (ne_of_gt hQ) (ne_of_gt hD)]
    simp only [braytonLossyHeatIn, braytonLossyCompressedTemp]
    field_simp
    ring

/-- Back-work ratio: for `0 < R < cp`, `rp > 1`, `T₃ > 0`, `ηc > 0` and `ηt > 0`, the compressor
input `cp (T₂ - T₁)` over the turbine output `cp (T₃ - T₄)` is `a T₁ / (ηc ηt T₃)`. -/
lemma braytonLossy_backWorkRatio {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₃ : 0 < T₃) (hηc : 0 < ηc) (hηt : 0 < ηt) :
    cp * (braytonLossyCompressedTemp T₁ rp R cp ηc - T₁) /
        (cp * (T₃ - braytonLossyExpandedTemp T₃ rp R cp ηt)) =
      braytonTempRatio rp R cp * T₁ / (ηc * ηt * T₃) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hηc0 : ηc ≠ 0 := ne_of_gt hηc
  have hturb : cp * (T₃ - braytonLossyExpandedTemp T₃ rp R cp ηt) =
      cp * (ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp)) := by
    simp only [braytonLossyExpandedTemp]
    ring
  have hden : 0 < cp * (T₃ - braytonLossyExpandedTemp T₃ rp R cp ηt) := by
    rw [hturb]
    exact mul_pos hcp (mul_pos (mul_pos hηt hT₃) hc)
  rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt (mul_pos (mul_pos hηc hηt) hT₃))]
  simp only [braytonLossyCompressedTemp, braytonLossyExpandedTemp]
  field_simp
  ring

/-! ### C.3. The positive-work threshold -/

/-- **The positive-work threshold.** For `0 < R < cp`, `rp > 1`, `ηc > 0` and `T₃ > 0`, the
nonideal loop does positive net work exactly when `ηc ηt > a T₁ / T₃`. -/
lemma braytonLossyNetWork_pos_iff {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hηc : 0 < ηc) (hT₃ : 0 < T₃) :
    0 < braytonLossyNetWork T₁ T₃ rp R cp ηc ηt ↔
      braytonTempRatio rp R cp * T₁ / T₃ < ηc * ηt := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hK : 0 < cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ / ηc) :=
    mul_pos (mul_pos hcp hc) (div_pos hT₃ hηc)
  rw [braytonLossyNetWork_eq_mul (lt_trans zero_lt_one hrp) (ne_of_gt hηc) (ne_of_gt hT₃),
    mul_pos_iff_of_pos_left hK, sub_pos]

/-- The threshold itself: for `0 < R < cp`, `rp > 1`, `ηc > 0` and `T₃ > 0`, the net work is zero
exactly when `ηc ηt = a T₁ / T₃`. -/
lemma braytonLossyNetWork_eq_zero_iff {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hηc : 0 < ηc) (hT₃ : 0 < T₃) :
    braytonLossyNetWork T₁ T₃ rp R cp ηc ηt = 0 ↔
      ηc * ηt = braytonTempRatio rp R cp * T₁ / T₃ := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hK : 0 < cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ / ηc) :=
    mul_pos (mul_pos hcp hc) (div_pos hT₃ hηc)
  rw [braytonLossyNetWork_eq_mul (lt_trans zero_lt_one hrp) (ne_of_gt hηc) (ne_of_gt hT₃),
    mul_eq_zero, sub_eq_zero, or_iff_right (ne_of_gt hK)]

/-! ### C.4. Monotonicity in the component efficiencies -/

/-- The work rises with the compressor efficiency: for `0 < R < cp`, `rp > 1` and `T₁ > 0`, the
net work is strictly increasing in `ηc` on `(0, 1]`, for every real `T₃` and `ηt`. -/
lemma braytonLossyNetWork_strictMonoOn_compressorEff {cp R rp T₁ T₃ ηt : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 1 < rp) (hT₁ : 0 < T₁) :
    StrictMonoOn (fun ηc => braytonLossyNetWork T₁ T₃ rp R cp ηc ηt) (Set.Ioc 0 1) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have hb : 0 < T₁ * (braytonTempRatio rp R cp - 1) := mul_pos hT₁ (sub_pos.mpr ha1)
  intro x hx y _ hxy
  have h : T₁ * (braytonTempRatio rp R cp - 1) / y < T₁ * (braytonTempRatio rp R cp - 1) / x :=
    div_lt_div_of_pos_left hb hx.1 hxy
  have h' := mul_lt_mul_of_pos_left h hcp
  simp only [braytonLossyNetWork, braytonLossyCompressedTemp]
  linarith

/-- The work rises with the turbine efficiency: for `0 < R < cp`, `rp > 1` and `T₃ > 0`, the net
work is strictly increasing in `ηt` on `(0, 1]`, for every real `T₁` and `ηc`. -/
lemma braytonLossyNetWork_strictMonoOn_turbineEff {cp R rp T₁ T₃ ηc : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 1 < rp) (hT₃ : 0 < T₃) :
    StrictMonoOn (braytonLossyNetWork T₁ T₃ rp R cp ηc) (Set.Ioc 0 1) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  intro x _ y _ hxy
  have hkey : braytonLossyNetWork T₁ T₃ rp R cp ηc y - braytonLossyNetWork T₁ T₃ rp R cp ηc x =
      cp * T₃ * (1 - 1 / braytonTempRatio rp R cp) * (y - x) := by
    simp only [braytonLossyNetWork, braytonLossyExpandedTemp]
    ring
  have hpos : 0 < cp * T₃ * (1 - 1 / braytonTempRatio rp R cp) * (y - x) :=
    mul_pos (mul_pos (mul_pos hcp hT₃) hc) (sub_pos.mpr hxy)
  linarith

/-- The efficiency rises with the compressor efficiency on positive heat input: for `0 < R < cp`,
`rp > 1`, `T₁ > 0` and `ηt ≤ 1`, the thermal efficiency is strictly increasing in `ηc` on the
compressor efficiencies in `(0, 1]` with `T₂ < T₃`. -/
lemma braytonLossyEfficiency_strictMonoOn_compressorEff {cp R rp T₁ T₃ ηt : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 1 < rp) (hT₁ : 0 < T₁) (hηt₁ : ηt ≤ 1) :
    StrictMonoOn (fun ηc => braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt)
      (Set.Ioc 0 1 ∩ {ηc | braytonLossyCompressedTemp T₁ rp R cp ηc < T₃}) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hb : 0 < T₁ * (braytonTempRatio rp R cp - 1) := mul_pos hT₁ (sub_pos.mpr ha1)
  rintro x ⟨⟨hx0, hx1⟩, hxT⟩ y ⟨⟨hy0, -⟩, hyT⟩ hxy
  replace hxT : braytonLossyCompressedTemp T₁ rp R cp x < T₃ := hxT
  replace hyT : braytonLossyCompressedTemp T₁ rp R cp y < T₃ := hyT
  have hT₂x : braytonTempRatio rp R cp * T₁ ≤ braytonLossyCompressedTemp T₁ rp R cp x := by
    simp only [braytonLossyCompressedTemp]
    have h : T₁ * (braytonTempRatio rp R cp - 1) ≤ T₁ * (braytonTempRatio rp R cp - 1) / x := by
      rw [le_div_iff₀ hx0]
      nlinarith
    linarith
  have hT₃a : braytonTempRatio rp R cp * T₁ < T₃ := lt_of_le_of_lt hT₂x hxT
  have hT₃ : 0 < T₃ := lt_trans (mul_pos ha hT₁) hT₃a
  have hBA : 0 < T₃ - T₁ - ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp) := by
    have h1 : ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp) ≤
        T₃ * (1 - 1 / braytonTempRatio rp R cp) := by nlinarith [mul_pos hT₃ hc]
    have h2 : T₃ * (1 - 1 / braytonTempRatio rp R cp) = T₃ - T₃ / braytonTempRatio rp R cp := by
      ring
    have h3 : T₁ < T₃ / braytonTempRatio rp R cp := by
      rw [lt_div_iff₀ ha]
      linarith
    linarith
  have hQx : 0 < braytonLossyHeatIn T₁ T₃ rp R cp x := by
    simp only [braytonLossyHeatIn]
    exact mul_pos hcp (sub_pos.mpr hxT)
  have hQy : 0 < braytonLossyHeatIn T₁ T₃ rp R cp y := by
    simp only [braytonLossyHeatIn]
    exact mul_pos hcp (sub_pos.mpr hyT)
  simp only [braytonLossyEfficiency]
  rw [div_lt_div_iff₀ hQx hQy]
  have hkey : braytonLossyNetWork T₁ T₃ rp R cp y ηt * braytonLossyHeatIn T₁ T₃ rp R cp x -
      braytonLossyNetWork T₁ T₃ rp R cp x ηt * braytonLossyHeatIn T₁ T₃ rp R cp y =
      cp ^ 2 * (T₁ * (braytonTempRatio rp R cp - 1)) * (1 / x - 1 / y) *
        (T₃ - T₁ - ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp)) := by
    simp only [braytonLossyNetWork, braytonLossyHeatIn, braytonLossyCompressedTemp,
      braytonLossyExpandedTemp]
    ring
  have hxy' : 0 < 1 / x - 1 / y := sub_pos.mpr (one_div_lt_one_div_of_lt hx0 hxy)
  have hpos : 0 < cp ^ 2 * (T₁ * (braytonTempRatio rp R cp - 1)) * (1 / x - 1 / y) *
      (T₃ - T₁ - ηt * T₃ * (1 - 1 / braytonTempRatio rp R cp)) :=
    mul_pos (mul_pos (mul_pos (pow_pos hcp 2) hb) hxy') hBA
  linarith

/-- The efficiency rises with the turbine efficiency on positive heat input: for `0 < R < cp`,
`rp > 1`, `T₁ > 0`, `ηc > 0` and `T₃ > T₂`, the thermal efficiency is strictly increasing in `ηt`
on `(0, 1]`. -/
lemma braytonLossyEfficiency_strictMonoOn_turbineEff {cp R rp T₁ T₃ ηc : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 1 < rp) (hT₁ : 0 < T₁) (hηc : 0 < ηc)
    (hT₃ : braytonLossyCompressedTemp T₁ rp R cp ηc < T₃) :
    StrictMonoOn (braytonLossyEfficiency T₁ T₃ rp R cp ηc) (Set.Ioc 0 1) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have hT₃pos : 0 < T₃ := lt_trans (braytonLossyCompressedTemp_pos hR hRcp hrp hT₁ hηc) hT₃
  have hQ : 0 < braytonLossyHeatIn T₁ T₃ rp R cp ηc := by
    simp only [braytonLossyHeatIn]
    exact mul_pos hcp (sub_pos.mpr hT₃)
  intro x hx y hy hxy
  simp only [braytonLossyEfficiency]
  exact div_lt_div_of_pos_right
    (braytonLossyNetWork_strictMonoOn_turbineEff hR hRcp hrp hT₃pos hx hy hxy) hQ

/-- **Losses lower the efficiency.** For `0 < R < cp`, `rp > 1`, `T₁ > 0`, `0 < ηc ≤ 1`, `ηt ≤ 1`
and positive heat input `T₃ > T₂`, the thermal efficiency is at most the ideal `1 - 1 / a`, with
equality exactly when `ηc = ηt = 1`. -/
lemma braytonLossyEfficiency_le_braytonEfficiency {cp R rp T₁ T₃ ηc ηt : ℝ} (hR : 0 < R)
    (hRcp : R < cp) (hrp : 1 < rp) (hT₁ : 0 < T₁) (hηc : 0 < ηc) (hηc₁ : ηc ≤ 1) (hηt₁ : ηt ≤ 1)
    (hT₃ : braytonLossyCompressedTemp T₁ rp R cp ηc < T₃) :
    braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt ≤ braytonEfficiency rp R cp ∧
      (braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt = braytonEfficiency rp R cp ↔
        ηc = 1 ∧ ηt = 1) := by
  have hcp : 0 < cp := lt_trans hR hRcp
  have ha1 := one_lt_braytonTempRatio hR hRcp hrp
  have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
  have ha0 : braytonTempRatio rp R cp ≠ 0 := ne_of_gt ha
  have hηc0 : ηc ≠ 0 := ne_of_gt hηc
  have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
  have hT₃pos : 0 < T₃ := lt_trans (braytonLossyCompressedTemp_pos hR hRcp hrp hT₁ hηc) hT₃
  have hQ : 0 < braytonLossyHeatIn T₁ T₃ rp R cp ηc := by
    simp only [braytonLossyHeatIn]
    exact mul_pos hcp (sub_pos.mpr hT₃)
  have hloss : braytonEfficiency rp R cp * braytonLossyHeatIn T₁ T₃ rp R cp ηc -
      braytonLossyNetWork T₁ T₃ rp R cp ηc ηt =
      cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ * (1 - ηt) + T₁ * (1 / ηc - 1)) := by
    simp only [braytonEfficiency, braytonLossyHeatIn, braytonLossyNetWork,
      braytonLossyCompressedTemp, braytonLossyExpandedTemp]
    field_simp
    ring
  have hdiff : braytonEfficiency rp R cp - braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt =
      cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ * (1 - ηt) + T₁ * (1 / ηc - 1)) /
        braytonLossyHeatIn T₁ T₃ rp R cp ηc := by
    rw [← hloss, braytonLossyEfficiency, sub_div, mul_div_assoc, div_self (ne_of_gt hQ),
      mul_one]
  have hK : 0 < cp * (1 - 1 / braytonTempRatio rp R cp) := mul_pos hcp hc
  have hL1 : 0 ≤ T₃ * (1 - ηt) := mul_nonneg (le_of_lt hT₃pos) (sub_nonneg.mpr hηt₁)
  have hL2 : 0 ≤ T₁ * (1 / ηc - 1) :=
    mul_nonneg (le_of_lt hT₁) (sub_nonneg.mpr ((one_le_div hηc).mpr hηc₁))
  refine ⟨?_, ⟨fun heq => ?_, fun h => ?_⟩⟩
  · have h : 0 ≤ braytonEfficiency rp R cp - braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt := by
      rw [hdiff]
      exact div_nonneg (mul_nonneg (le_of_lt hK) (add_nonneg hL1 hL2)) (le_of_lt hQ)
    linarith
  · have h0 : cp * (1 - 1 / braytonTempRatio rp R cp) * (T₃ * (1 - ηt) + T₁ * (1 / ηc - 1)) /
        braytonLossyHeatIn T₁ T₃ rp R cp ηc = 0 := by
      rw [← hdiff, heq, sub_self]
    rw [div_eq_zero_iff, mul_eq_zero, or_iff_right (ne_of_gt hK),
      or_iff_left (ne_of_gt hQ)] at h0
    have h1 : T₃ * (1 - ηt) = 0 := by linarith
    have h2 : T₁ * (1 / ηc - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact absurd h1 (ne_of_gt hT₃pos)
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 (ne_of_gt hT₁)
    have h3 : 1 / ηc = 1 := by linarith
    exact ⟨((div_eq_one_iff_eq hηc0).mp h3).symm, by linarith⟩
  · obtain ⟨rfl, rfl⟩ := h
    have h0 : braytonEfficiency rp R cp - braytonLossyEfficiency T₁ T₃ rp R cp 1 1 = 0 := by
      rw [hdiff]
      simp
    linarith

/-! ## D. Regeneration without heat-flow reversal -/

open HeatTransfer.HeatExchangers

/-! ### D.1. Regenerator ports -/

/-- Temperature `T₅` of the compressed stream leaving the regenerator, the combustor inlet. The
regenerator is a counterflow exchanger with the turbine exhaust as the hot stream (inlet `T₄`)
and the compressed stream as the cold stream (inlet `T₂`), both at the capacity rate `cp` per unit
mass flow, and conductance `UA` per unit mass flow. When the exhaust is hotter, `T₂ < T₄`, the
compressed stream leaves at `T₂ + ε (T₄ - T₂)` with the counterflow effectiveness
`ε = counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp)`; otherwise the
regenerator is bypassed and `T₅ = T₂`. Physical domain `cp > 0` and `UA ≥ 0`. -/
noncomputable def braytonRegenPreheatTemp (T₁ T₃ rp R cp ηc ηt UA : ℝ) : ℝ :=
  if braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt then
    braytonLossyCompressedTemp T₁ rp R cp ηc +
      counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) *
        (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc)
  else braytonLossyCompressedTemp T₁ rp R cp ηc

/-- Temperature `T₆` of the exhaust leaving the regenerator: `T₄ - ε (T₄ - T₂)` when the exhaust
is hotter than the compressed stream, `T₂ < T₄`, and `T₄` in the bypass otherwise. -/
noncomputable def braytonRegenExhaustTemp (T₁ T₃ rp R cp ηc ηt UA : ℝ) : ℝ :=
  if braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt then
    braytonLossyExpandedTemp T₃ rp R cp ηt -
      counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) *
        (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc)
  else braytonLossyExpandedTemp T₃ rp R cp ηt

/-- Heat recovered per unit mass by the regenerator, the heat gained by the compressed stream,
`Q_reg = cp (T₅ - T₂)`. -/
noncomputable def braytonRegenHeat (T₁ T₃ rp R cp ηc ηt UA : ℝ) : ℝ :=
  cp * (braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA -
    braytonLossyCompressedTemp T₁ rp R cp ηc)

/-- External heat demand per unit mass of the regenerated loop, the heat added on the isobaric leg
from the regenerator outlet to the turbine inlet, `Qin_reg = cp (T₃ - T₅)`. -/
noncomputable def braytonRegenHeatIn (T₁ T₃ rp R cp ηc ηt UA : ℝ) : ℝ :=
  cp * (T₃ - braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA)

/-- **The regenerator runs at equal capacity rates.** For `cp > 0` and `UA ≥ 0` the regenerator
streams have `Cr = 1` and `NTU = UA / cp`, so the counterflow effectiveness is its equal-capacity
branch `ε = UA / (cp + UA)`, not the general formula's `0 / 0`, and `0 ≤ ε < 1`. -/
lemma braytonRegen_effectiveness {cp UA : ℝ} (hcp : 0 < cp) (hUA : 0 ≤ UA) :
    capacityRatio cp cp = 1 ∧ transferUnits UA cp cp = UA / cp ∧
      counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) = UA / (cp + UA) ∧
      0 ≤ counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) ∧
      counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) < 1 := by
  have hcp0 : cp ≠ 0 := hcp.ne'
  have hsum : 0 < cp + UA := by linarith
  have hsum0 : cp + UA ≠ 0 := hsum.ne'
  have hdom := capacityRatio_domain hcp hcp hUA
  have hCr : capacityRatio cp cp = 1 := hdom.2.2.1.mpr rfl
  have hN : transferUnits UA cp cp = UA / cp := by
    unfold transferUnits
    rw [min_self]
  have hE : counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) =
      UA / (cp + UA) := by
    rw [hCr, hN]
    unfold counterflowEffectiveness
    rw [ite_eq_left rfl]
    field_simp
  refine ⟨hCr, hN, hE, (counterflowEffectiveness_bounds hdom.2.2.2 hdom.2.1).1, ?_⟩
  rw [hE, div_lt_one hsum]
  linarith

/-- **An exhaust hotter than the compressed stream feeds the exchanger.** For every real
parameter with `T₂ < T₄`: `T₅ = T₂ + ε (T₄ - T₂)`, `T₆ = T₄ - ε (T₄ - T₂)`, and the recovered heat
is the effectiveness contract `Q_reg = ε Cmin (T₄ - T₂)` with `Cmin = min cp cp`. -/
lemma braytonRegen_of_lt {cp R rp T₁ T₃ ηc ηt UA : ℝ}
    (hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt) :
    braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA = braytonLossyCompressedTemp T₁ rp R cp ηc +
        counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) *
          (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc) ∧
      braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA = braytonLossyExpandedTemp T₃ rp R cp ηt -
        counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) *
          (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc) ∧
      braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA =
        counterflowEffectiveness (transferUnits UA cp cp) (capacityRatio cp cp) * min cp cp *
          (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc) := by
  refine ⟨ite_eq_left hT, ite_eq_left hT, ?_⟩
  rw [braytonRegenHeat, braytonRegenPreheatTemp, ite_eq_left hT, min_self]
  ring

/-- **Otherwise the regenerator is bypassed.** For every real parameter with `T₄ ≤ T₂`, equality
included, both streams pass unchanged, `T₅ = T₂` and `T₆ = T₄`; no heat is recovered, the external
heat demand is the heat input `Qin` of section C, and the work-to-heat ratio is that of section C:
no efficiency benefit for a backward temperature gradient. -/
lemma braytonRegen_bypass {cp R rp T₁ T₃ ηc ηt UA : ℝ}
    (hT : braytonLossyExpandedTemp T₃ rp R cp ηt ≤ braytonLossyCompressedTemp T₁ rp R cp ηc) :
    braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA = braytonLossyCompressedTemp T₁ rp R cp ηc ∧
      braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA = braytonLossyExpandedTemp T₃ rp R cp ηt ∧
      braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA = 0 ∧
      braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA = braytonLossyHeatIn T₁ T₃ rp R cp ηc ∧
      braytonLossyNetWork T₁ T₃ rp R cp ηc ηt / braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA =
        braytonLossyEfficiency T₁ T₃ rp R cp ηc ηt := by
  have hnot := not_lt.mpr hT
  have h5 : braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA =
      braytonLossyCompressedTemp T₁ rp R cp ηc := ite_eq_right hnot
  have hQin : braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA =
      braytonLossyHeatIn T₁ T₃ rp R cp ηc := by
    rw [braytonRegenHeatIn, h5, braytonLossyHeatIn]
  refine ⟨h5, ite_eq_right hnot, ?_, hQin, ?_⟩
  · rw [braytonRegenHeat, h5, sub_self, mul_zero]
  · rw [hQin, braytonLossyEfficiency]

/-- **Heat balance of the regenerated loop.** For every real parameter, on both branches: the heat
lost by the exhaust equals the heat gained by the compressed stream, `cp (T₄ - T₆) = Q_reg`; the
external heat demand is the heat input of section C less that heat, `Qin_reg = Qin - Q_reg`; and
the net work is unchanged, `Wnet = Qin_reg - cp (T₆ - T₁)`. -/
lemma braytonRegen_heat_balance (T₁ T₃ rp R cp ηc ηt UA : ℝ) :
    cp * (braytonLossyExpandedTemp T₃ rp R cp ηt -
        braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA) =
        braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA ∧
      braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA =
        braytonLossyHeatIn T₁ T₃ rp R cp ηc - braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA ∧
      braytonLossyNetWork T₁ T₃ rp R cp ηc ηt = braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA -
        cp * (braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA - T₁) := by
  simp only [braytonRegenHeat, braytonRegenHeatIn, braytonRegenPreheatTemp,
    braytonRegenExhaustTemp, braytonLossyHeatIn, braytonLossyNetWork]
  split_ifs <;> exact ⟨by ring, by ring, by ring⟩

/-! ### D.2. No heat-flow reversal -/

/-- **No negative heat recovery.** For `cp > 0` and `UA ≥ 0`, whatever the order of `T₂` and
`T₄`, the recovered heat is nonnegative: an exhaust that is not hotter is bypassed instead of
taking heat from the compressed stream. -/
lemma braytonRegenHeat_nonneg {cp R rp T₁ T₃ ηc ηt UA : ℝ} (hcp : 0 < cp) (hUA : 0 ≤ UA) :
    0 ≤ braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA := by
  by_cases hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt
  · rw [(braytonRegen_of_lt (UA := UA) hT).2.2, min_self]
    exact mul_nonneg (mul_nonneg (braytonRegen_effectiveness hcp hUA).2.2.2.1 hcp.le)
      (sub_nonneg.mpr hT.le)
  · exact le_of_eq (braytonRegen_bypass (UA := UA) (not_lt.mp hT)).2.2.1.symm

/-- **Heat is recovered exactly from a hotter exhaust.** For `cp > 0` and `UA ≥ 0`, `Q_reg > 0` if
and only if `T₂ < T₄` and `UA > 0`; at equal temperatures nothing is recovered. -/
lemma braytonRegenHeat_pos_iff {cp R rp T₁ T₃ ηc ηt UA : ℝ} (hcp : 0 < cp) (hUA : 0 ≤ UA) :
    0 < braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA ↔
      braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt ∧
        0 < UA := by
  obtain ⟨-, -, hE, -, -⟩ := braytonRegen_effectiveness hcp hUA
  by_cases hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt
  · rw [(braytonRegen_of_lt (UA := UA) hT).2.2, min_self, hE]
    have hd := sub_pos.mpr hT
    have hsum : 0 < cp + UA := by linarith
    refine ⟨fun h => ⟨hT, ?_⟩, fun h => mul_pos (mul_pos (div_pos h.2 hsum) hcp) hd⟩
    rcases hUA.lt_or_eq with hpos | h0
    · exact hpos
    · rw [← h0, zero_div, zero_mul, zero_mul] at h
      exact absurd h (lt_irrefl 0)
  · rw [(braytonRegen_bypass (UA := UA) (not_lt.mp hT)).2.2.1]
    exact ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h.1 hT⟩

/-- **The external heat demand falls exactly when heat is recovered.** For `cp > 0` and `UA ≥ 0`,
`Qin_reg ≤ Qin`, with `Qin_reg < Qin` if and only if `T₂ < T₄` and `UA > 0`. -/
lemma braytonRegenHeatIn_le_braytonLossyHeatIn {cp R rp T₁ T₃ ηc ηt UA : ℝ} (hcp : 0 < cp)
    (hUA : 0 ≤ UA) :
    braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA ≤ braytonLossyHeatIn T₁ T₃ rp R cp ηc ∧
      (braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA < braytonLossyHeatIn T₁ T₃ rp R cp ηc ↔
        braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt ∧
          0 < UA) := by
  have hbal := (braytonRegen_heat_balance T₁ T₃ rp R cp ηc ηt UA).2.1
  have hnn : 0 ≤ braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA := braytonRegenHeat_nonneg hcp hUA
  have hpos : 0 < braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA ↔
      braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt ∧
        0 < UA := braytonRegenHeat_pos_iff hcp hUA
  rw [hbal, ← hpos]
  exact ⟨sub_le_self _ hnn, sub_lt_self_iff _⟩

/-- **Heat flows only from the exhaust to the compressed stream.** For `cp > 0`, `UA ≥ 0` and
`T₂ < T₄`, the compressed stream is never cooled and stays below the exhaust inlet,
`T₂ ≤ T₅ < T₄`, and the exhaust is never heated and stays above the compressed-stream inlet,
`T₂ < T₆ ≤ T₄`. No order
between `T₅` and `T₆` is asserted: a counterflow temperature cross `T₆ < T₅` is allowed. -/
lemma braytonRegen_temp_order {cp R rp T₁ T₃ ηc ηt UA : ℝ} (hcp : 0 < cp) (hUA : 0 ≤ UA)
    (hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt) :
    braytonLossyCompressedTemp T₁ rp R cp ηc ≤ braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA ∧
      braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA < braytonLossyExpandedTemp T₃ rp R cp ηt ∧
      braytonLossyCompressedTemp T₁ rp R cp ηc < braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA ∧
      braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA ≤ braytonLossyExpandedTemp T₃ rp R cp ηt := by
  obtain ⟨h5, h6, -⟩ := braytonRegen_of_lt (UA := UA) hT
  obtain ⟨-, -, -, hE0, hE1⟩ := braytonRegen_effectiveness hcp hUA
  have hd := sub_pos.mpr hT
  have h1 := mul_nonneg hE0 hd.le
  have h2 := mul_lt_mul_of_pos_right hE1 hd
  rw [h5, h6]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The regenerated loop still takes heat from outside.** For `0 < R < cp`, `rp > 1`, `T₃ > 0`,
`ηt > 0`, `UA ≥ 0` and positive heat input of section C, `T₂ < T₃`, the regenerator never brings
the compressed stream up to the turbine inlet: `Qin_reg > 0`. -/
lemma braytonRegenHeatIn_pos {cp R rp T₁ T₃ ηc ηt UA : ℝ} (hR : 0 < R) (hRcp : R < cp)
    (hrp : 1 < rp) (hT₃ : 0 < T₃) (hηt : 0 < ηt) (hUA : 0 ≤ UA)
    (hQ : braytonLossyCompressedTemp T₁ rp R cp ηc < T₃) :
    0 < braytonRegenHeatIn T₁ T₃ rp R cp ηc ηt UA := by
  have hcp : 0 < cp := lt_trans hR hRcp
  rw [braytonRegenHeatIn]
  refine mul_pos hcp (sub_pos.mpr ?_)
  by_cases hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt
  · have ha1 := one_lt_braytonTempRatio hR hRcp hrp
    have ha : 0 < braytonTempRatio rp R cp := lt_trans zero_lt_one ha1
    have hc : 0 < 1 - 1 / braytonTempRatio rp R cp := sub_pos.mpr ((div_lt_one ha).mpr ha1)
    have h4 : braytonLossyExpandedTemp T₃ rp R cp ηt < T₃ := by
      have h := mul_pos (mul_pos hηt hT₃) hc
      simp only [braytonLossyExpandedTemp]
      linarith
    exact lt_trans (braytonRegen_temp_order hcp hUA hT).2.1 h4
  · rw [(braytonRegen_bypass (UA := UA) (not_lt.mp hT)).1]
    exact hQ

/-! ### D.3. The counterflow exchanger between the ports -/

/-- **The ports are the outlets of every counterflow solution.** For `cp > 0`, `UA ≥ 0`, `L > 0`
and `T₂ < T₄`, let `(Th, Tc)` solve the counterflow equations with the exhaust as the hot stream
(inlet `T₄` at `x = 0`) and the compressed stream as the cold stream (inlet `T₂` at `x = L`), both
at capacity rate `cp` per unit mass flow, with conductance `UA / L` per unit length. Its cold
outlet is `T₅`, its hot outlet is `T₆`, and the heat gained by the compressed stream equals the
heat lost by the exhaust: `cp (Tc 0 - T₂) = cp (T₄ - Th L) = Q_reg`. -/
lemma braytonRegen_of_isCounterflowSolution {cp R rp T₁ T₃ ηc ηt UA L : ℝ} {Th Tc : ℝ → ℝ}
    (hcp : 0 < cp) (hUA : 0 ≤ UA) (hL : 0 < L)
    (hT : braytonLossyCompressedTemp T₁ rp R cp ηc < braytonLossyExpandedTemp T₃ rp R cp ηt)
    (h : IsCounterflowSolution cp cp (UA / L) L (braytonLossyExpandedTemp T₃ rp R cp ηt)
      (braytonLossyCompressedTemp T₁ rp R cp ηc) Th Tc) :
    Tc 0 = braytonRegenPreheatTemp T₁ T₃ rp R cp ηc ηt UA ∧
      Th L = braytonRegenExhaustTemp T₁ T₃ rp R cp ηc ηt UA ∧
      cp * (Tc 0 - braytonLossyCompressedTemp T₁ rp R cp ηc) =
        braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA ∧
      cp * (braytonLossyExpandedTemp T₃ rp R cp ηt - Th L) =
        braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA := by
  obtain ⟨hhot, hcold⟩ := h.heat_eq_effectiveness hcp hcp hUA hL
  obtain ⟨h5, h6, hQ⟩ := braytonRegen_of_lt (UA := UA) hT
  rw [min_self] at hhot hcold hQ
  have hcp0 : cp ≠ 0 := hcp.ne'
  refine ⟨?_, ?_, hcold.trans hQ.symm, hhot.trans hQ.symm⟩
  · rw [h5]
    exact mul_left_cancel₀ hcp0 (by linear_combination hcold)
  · rw [h6]
    exact mul_left_cancel₀ hcp0 (by linear_combination -hhot)

/-- **Against the gradient the exchanger would reverse the heat flow.** For `cp > 0`, `UA > 0`,
`L > 0` and an exhaust colder than the compressed stream, `T₄ < T₂`, a counterflow solution
connected as above would cool the compressed stream, `Tc 0 < T₂`, and heat the exhaust,
`T₄ < Th L`: negative heat recovery. The regenerator ports bypass instead, with `Q_reg = 0`. -/
lemma braytonRegen_reversal_of_isCounterflowSolution {cp R rp T₁ T₃ ηc ηt UA L : ℝ}
    {Th Tc : ℝ → ℝ} (hcp : 0 < cp) (hUA : 0 < UA) (hL : 0 < L)
    (hT : braytonLossyExpandedTemp T₃ rp R cp ηt < braytonLossyCompressedTemp T₁ rp R cp ηc)
    (h : IsCounterflowSolution cp cp (UA / L) L (braytonLossyExpandedTemp T₃ rp R cp ηt)
      (braytonLossyCompressedTemp T₁ rp R cp ηc) Th Tc) :
    Tc 0 < braytonLossyCompressedTemp T₁ rp R cp ηc ∧
      braytonLossyExpandedTemp T₃ rp R cp ηt < Th L ∧
      braytonRegenHeat T₁ T₃ rp R cp ηc ηt UA = 0 := by
  obtain ⟨hhot, hcold⟩ := h.heat_eq_effectiveness hcp hcp hUA.le hL
  obtain ⟨-, -, hE, -, -⟩ := braytonRegen_effectiveness hcp hUA.le
  rw [min_self, hE] at hhot hcold
  have hneg : UA / (cp + UA) * cp *
      (braytonLossyExpandedTemp T₃ rp R cp ηt - braytonLossyCompressedTemp T₁ rp R cp ηc) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (div_pos hUA (by linarith)) hcp) (sub_neg.mpr hT)
  refine ⟨?_, ?_, (braytonRegen_bypass (UA := UA) hT.le).2.2.1⟩
  · by_contra hge
    have := mul_nonneg hcp.le (sub_nonneg.mpr (not_lt.mp hge))
    linarith
  · by_contra hge
    have := mul_nonneg hcp.le (sub_nonneg.mpr (not_lt.mp hge))
    linarith

/-! ## E. Property-table enclosure at the cycle port -/

open MathlibExt.Analysis.Numerical.Certified

/-! ### E.1. Tables, lookups and the supplied envelope -/

/-- A property table of specific enthalpy against absolute temperature: nodes `(Tₖ, hₖ)`, exact
rationals in K and J/kg, with strictly increasing positive temperatures (a monotone table), and a
supplied interpolation-error envelope `ε ≥ 0`. The entries are supplied data; no theorem infers
or certifies them. -/
structure PropertyTable where
  /-- The tabulated nodes `(Tₖ, hₖ)`. -/
  nodes : List (ℚ × ℚ)
  /-- The temperatures strictly increase along the table. -/
  sorted : nodes.Pairwise fun a b => a.1 < b.1
  /-- The tabulated temperatures are absolute, hence positive. -/
  temp_pos : ∀ n ∈ nodes, 0 < n.1
  /-- The supplied interpolation-error envelope `ε`. -/
  envelope : ℚ
  /-- The envelope is a nonnegative bound. -/
  envelope_nonneg : 0 ≤ envelope

/-- Piecewise-linear interpolation through a node list at `T`: the first segment `[Tₖ, Tₖ₊₁]`
that contains `T` gives `hₖ + (hₖ₊₁ - hₖ) (T - Tₖ) / (Tₖ₊₁ - Tₖ)`, a single node gives its value
at its own temperature, and otherwise there is no value. On the nodes of a `PropertyTable` every
segment has positive width, so the division is never by zero. -/
def tableInterp : List (ℚ × ℚ) → ℚ → Option ℚ
  | [], _ => none
  | [a], T => if T = a.1 then some a.2 else none
  | a :: b :: rest, T =>
    if a.1 ≤ T ∧ T ≤ b.1 then some (a.2 + (b.2 - a.2) * (T - a.1) / (b.1 - a.1))
    else tableInterp (b :: rest) T

namespace PropertyTable

/-- `tab.InRange T`: the temperature `T` lies between two tabulated temperatures, that is, in the
table range from the first to the last node. -/
def InRange (tab : PropertyTable) (T : ℚ) : Prop :=
  ∃ a ∈ tab.nodes, ∃ b ∈ tab.nodes, a.1 ≤ T ∧ T ≤ b.1

/-- Certified enthalpy at `T`: the interpolant `q` widened by the envelope to the rational
interval `[q - ε, q + ε]` (`RatInterval.ofCenter`), or `none` where the table does not
interpolate. -/
def lookup (tab : PropertyTable) (T : ℚ) : Option RatInterval :=
  (tableInterp tab.nodes T).map fun q => RatInterval.ofCenter q tab.envelope

/-- `tab.WithinEnvelope h`: wherever the table interpolates, the declared property model `h`
(J/kg against K) lies within the supplied envelope of the interpolant, `|h T - q| ≤ ε`. A model
input, to be justified for the chosen model (for example from a bound on `h''` and the rounding
of the entries); no theorem derives it from the data. -/
def WithinEnvelope (tab : PropertyTable) (h : ℝ → ℝ) : Prop :=
  ∀ T q, tableInterp tab.nodes T = some q → |h T - q| ≤ tab.envelope

/-- Certified heat added per unit mass on the isobaric leg `2 → 3`, `h(T₃) - h(T₂)`: the
interval difference of the two port values, or `none` if either port temperature is outside the
table. -/
def heatInEnclosure (tab : PropertyTable) (T₂ T₃ : ℚ) : Option RatInterval :=
  match tab.lookup T₂, tab.lookup T₃ with
  | some I₂, some I₃ => some (I₃.sub I₂)
  | _, _ => none

/-- Certified heat rejected per unit mass on the closing isobaric leg `4 → 1`, `h(T₄) - h(T₁)`,
or `none` if either port temperature is outside the table. -/
def heatOutEnclosure (tab : PropertyTable) (T₁ T₄ : ℚ) : Option RatInterval :=
  match tab.lookup T₁, tab.lookup T₄ with
  | some I₁, some I₄ => some (I₄.sub I₁)
  | _, _ => none

/-- Certified net work output per unit mass (engineering sign): the turbine interval
`h(T₃) - h(T₄)` minus the compressor interval `h(T₂) - h(T₁)`, or `none` if any of the four port
temperatures is outside the table. -/
def netWorkEnclosure (tab : PropertyTable) (T₁ T₂ T₃ T₄ : ℚ) : Option RatInterval :=
  match tab.lookup T₁, tab.lookup T₂, tab.lookup T₃, tab.lookup T₄ with
  | some I₁, some I₂, some I₃, some I₄ => some ((I₃.sub I₄).sub (I₂.sub I₁))
  | _, _, _, _ => none

/-- On a strictly increasing node list the interpolant exists exactly between two node
temperatures. -/
private lemma tableInterp_isSome_iff : ∀ {l : List (ℚ × ℚ)} {T : ℚ},
    l.Pairwise (fun a b => a.1 < b.1) →
      ((tableInterp l T).isSome ↔ ∃ a ∈ l, ∃ b ∈ l, a.1 ≤ T ∧ T ≤ b.1)
  | [], _, _ => by simp [tableInterp]
  | [a], T, _ => by
    simp only [tableInterp, List.mem_singleton, exists_eq_left]
    by_cases hT : T = a.1
    · subst hT
      simp
    · simp only [hT, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_iff, not_and,
        not_le]
      intro h1
      exact lt_of_le_of_ne h1 fun h => hT h.symm
  | a :: b :: rest, T, hl => by
    have hab : a.1 < b.1 := (List.pairwise_cons.1 hl).1 b (by simp)
    have hmin : ∀ x ∈ a :: b :: rest, a.1 ≤ x.1 := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.1 hl).1 x hx)
    have ih := tableInterp_isSome_iff (l := b :: rest) (T := T) (List.pairwise_cons.1 hl).2
    simp only [tableInterp]
    by_cases hs : a.1 ≤ T ∧ T ≤ b.1
    · simp only [hs, and_self, ↓reduceIte, Option.isSome_some, true_iff]
      exact ⟨a, by simp, b, by simp, hs.1, hs.2⟩
    · simp only [hs, ↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨x, hx, y, hy, hxT, hTy⟩
        exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hxT, hTy⟩
      · rintro ⟨x, hx, y, hy, hxT, hTy⟩
        have hbT : b.1 < T := by
          by_contra hbT
          exact hs ⟨le_trans (hmin x hx) hxT, le_of_not_gt hbT⟩
        refine ⟨b, by simp, y, ?_, le_of_lt hbT, hTy⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd (lt_of_lt_of_le (lt_trans hab hbT) hTy) (lt_irrefl _)
        · exact hy

/-- A certified value is the interpolant widened by the envelope. -/
private lemma lookup_eq_some {tab : PropertyTable} {T : ℚ} {I : RatInterval}
    (hI : tab.lookup T = some I) :
    ∃ q, tableInterp tab.nodes T = some q ∧ I = RatInterval.ofCenter q tab.envelope := by
  unfold lookup at hI
  cases hq : tableInterp tab.nodes T with
  | none => simp [hq] at hI
  | some q =>
    rw [hq] at hI
    exact ⟨q, rfl, (Option.some.inj hI).symm⟩

/-- Interval subtraction adds the widths. -/
private lemma width_sub (I J : RatInterval) : (I.sub J).width = I.width + J.width := by
  simp only [RatInterval.width, RatInterval.sub_lower, RatInterval.sub_upper]
  ring

/-- **Pointwise enclosure.** If the declared model `h` lies within the table's envelope, every
certified value encloses it: `tab.lookup T = some I` gives `h T ∈ I`. -/
lemma lookup_encloses {tab : PropertyTable} {h : ℝ → ℝ} {T : ℚ} {I : RatInterval}
    (htab : tab.WithinEnvelope h) (hI : tab.lookup T = some I) : I.Encloses (h T) := by
  obtain ⟨q, hq, rfl⟩ := lookup_eq_some hI
  exact RatInterval.encloses_ofCenter (htab T q hq)

/-- **No extrapolation.** The table returns no certified value exactly at the temperatures
outside its range: `tab.lookup T = none` if and only if `T` is not between two tabulated
temperatures. -/
lemma lookup_eq_none_iff {tab : PropertyTable} {T : ℚ} :
    tab.lookup T = none ↔ ¬ tab.InRange T := by
  have h := tableInterp_isSome_iff (T := T) tab.sorted
  unfold lookup InRange
  rw [Option.map_eq_none_iff, ← h, Option.not_isSome_iff_eq_none]

/-- Each certified port value carries exactly the supplied property error: its width is
`2 ε`. -/
lemma width_of_lookup_eq_some {tab : PropertyTable} {T : ℚ} {I : RatInterval}
    (hI : tab.lookup T = some I) : I.width = 2 * tab.envelope := by
  obtain ⟨q, -, rfl⟩ := lookup_eq_some hI
  simp only [RatInterval.width, RatInterval.ofCenter_lower, RatInterval.ofCenter_upper]
  ring

/-- A temperature in the table range is a positive absolute temperature. -/
lemma InRange.pos {tab : PropertyTable} {T : ℚ} (hT : tab.InRange T) : 0 < T := by
  obtain ⟨a, ha, -, -, haT, -⟩ := hT
  exact lt_of_lt_of_le (tab.temp_pos a ha) haT

/-! ### E.2. Port enclosures -/

/-- **Heat added.** If the declared model `h` lies within the table's envelope, the certified
heat added encloses `h(T₃) - h(T₂)` and has width `4 ε`. -/
lemma heatInEnclosure_encloses {tab : PropertyTable} {h : ℝ → ℝ} {T₂ T₃ : ℚ} {J : RatInterval}
    (htab : tab.WithinEnvelope h) (hJ : tab.heatInEnclosure T₂ T₃ = some J) :
    J.Encloses (h T₃ - h T₂) ∧ J.width = 4 * tab.envelope := by
  unfold heatInEnclosure at hJ
  rcases h₂ : tab.lookup T₂ with _ | I₂ <;> rcases h₃ : tab.lookup T₃ with _ | I₃ <;>
    simp only [h₂, h₃, reduceCtorEq, Option.some.injEq] at hJ
  subst hJ
  refine ⟨(lookup_encloses htab h₃).sub (lookup_encloses htab h₂), ?_⟩
  rw [width_sub, width_of_lookup_eq_some h₃, width_of_lookup_eq_some h₂]
  ring

/-- **Heat rejected.** If the declared model `h` lies within the table's envelope, the certified
heat rejected encloses `h(T₄) - h(T₁)` and has width `4 ε`. -/
lemma heatOutEnclosure_encloses {tab : PropertyTable} {h : ℝ → ℝ} {T₁ T₄ : ℚ} {J : RatInterval}
    (htab : tab.WithinEnvelope h) (hJ : tab.heatOutEnclosure T₁ T₄ = some J) :
    J.Encloses (h T₄ - h T₁) ∧ J.width = 4 * tab.envelope := by
  unfold heatOutEnclosure at hJ
  rcases h₁ : tab.lookup T₁ with _ | I₁ <;> rcases h₄ : tab.lookup T₄ with _ | I₄ <;>
    simp only [h₁, h₄, reduceCtorEq, Option.some.injEq] at hJ
  subst hJ
  refine ⟨(lookup_encloses htab h₄).sub (lookup_encloses htab h₁), ?_⟩
  rw [width_sub, width_of_lookup_eq_some h₄, width_of_lookup_eq_some h₁]
  ring

/-- **Net work.** If the declared model `h` lies within the table's envelope, the certified net
work encloses `(h(T₃) - h(T₄)) - (h(T₂) - h(T₁))` and has width `8 ε`. -/
lemma netWorkEnclosure_encloses {tab : PropertyTable} {h : ℝ → ℝ} {T₁ T₂ T₃ T₄ : ℚ}
    {J : RatInterval} (htab : tab.WithinEnvelope h)
    (hJ : tab.netWorkEnclosure T₁ T₂ T₃ T₄ = some J) :
    J.Encloses ((h T₃ - h T₄) - (h T₂ - h T₁)) ∧ J.width = 8 * tab.envelope := by
  unfold netWorkEnclosure at hJ
  rcases h₁ : tab.lookup T₁ with _ | I₁ <;> rcases h₂ : tab.lookup T₂ with _ | I₂ <;>
    rcases h₃ : tab.lookup T₃ with _ | I₃ <;> rcases h₄ : tab.lookup T₄ with _ | I₄ <;>
    simp only [h₁, h₂, h₃, h₄, reduceCtorEq, Option.some.injEq] at hJ
  subst hJ
  refine ⟨((lookup_encloses htab h₃).sub (lookup_encloses htab h₄)).sub
    ((lookup_encloses htab h₂).sub (lookup_encloses htab h₁)), ?_⟩
  rw [width_sub, width_sub, width_sub, width_of_lookup_eq_some h₁, width_of_lookup_eq_some h₂,
    width_of_lookup_eq_some h₃, width_of_lookup_eq_some h₄]
  ring

/-- **No extrapolation at the ports.** A composed heat or work value is missing exactly when one
of its port temperatures is outside the table range. -/
lemma portEnclosures_eq_none_iff {tab : PropertyTable} {T₁ T₂ T₃ T₄ : ℚ} :
    (tab.heatInEnclosure T₂ T₃ = none ↔ ¬ tab.InRange T₂ ∨ ¬ tab.InRange T₃) ∧
      (tab.heatOutEnclosure T₁ T₄ = none ↔ ¬ tab.InRange T₁ ∨ ¬ tab.InRange T₄) ∧
      (tab.netWorkEnclosure T₁ T₂ T₃ T₄ = none ↔
        ¬ tab.InRange T₁ ∨ ¬ tab.InRange T₂ ∨ ¬ tab.InRange T₃ ∨ ¬ tab.InRange T₄) := by
  simp only [← lookup_eq_none_iff]
  refine ⟨?_, ?_, ?_⟩
  · unfold heatInEnclosure
    cases tab.lookup T₂ <;> cases tab.lookup T₃ <;> simp
  · unfold heatOutEnclosure
    cases tab.lookup T₁ <;> cases tab.lookup T₄ <;> simp
  · unfold netWorkEnclosure
    cases tab.lookup T₁ <;> cases tab.lookup T₂ <;> cases tab.lookup T₃ <;>
      cases tab.lookup T₄ <;> simp

end PropertyTable

/-! ### E.3. Property error kept apart -/

/-- **Property error kept apart.** Let `J` enclose the declared-model value `x` at the computed
port temperatures (property error only), let the same model at the exact port states give `x'`,
with solver error `|x' - x| ≤ δs`, and let the physical value `y` differ from `x'` by the
physical-model error `|y - x'| ≤ δm`. Then `y` lies in `J` widened by `δs + δm`: each error enters
through its own declared bound, and neither is absorbed into the table envelope. -/
lemma encloses_sub_ofCenter_of_errors {J : RatInterval} {x x' y : ℝ} {δs δm : ℚ}
    (hJ : J.Encloses x) (hs : |x' - x| ≤ δs) (hm : |y - x'| ≤ δm) :
    (J.sub (RatInterval.ofCenter 0 (δs + δm))).Encloses y := by
  simp only [RatInterval.encloses_iff] at hJ ⊢
  simp only [RatInterval.sub_lower, RatInterval.sub_upper, RatInterval.ofCenter_lower,
    RatInterval.ofCenter_upper] at ⊢
  push_cast at ⊢
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  obtain ⟨hm1, hm2⟩ := abs_le.1 hm
  constructor <;> linarith

/-- **The section C loop inside the table enclosures.** Take the cold-air declared model
`h T = cp T` of section C, a table whose envelope holds for it, and rational port temperatures
equal to the section C states, `T₂ = braytonLossyCompressedTemp T₁ rp R cp ηc` and
`T₄ = braytonLossyExpandedTemp T₃ rp R cp ηt`. Then the certified heat added, heat rejected and
net work enclose `braytonLossyHeatIn`, `braytonLossyHeatOut` and `braytonLossyNetWork`. -/
lemma braytonLossy_encloses {tab : PropertyTable} {cp rp R ηc ηt : ℝ} {T₁ T₂ T₃ T₄ : ℚ}
    {J₁ J₂ J₃ : RatInterval} (htab : tab.WithinEnvelope fun T => cp * T)
    (hT₂ : (T₂ : ℝ) = braytonLossyCompressedTemp T₁ rp R cp ηc)
    (hT₄ : (T₄ : ℝ) = braytonLossyExpandedTemp T₃ rp R cp ηt)
    (hin : tab.heatInEnclosure T₂ T₃ = some J₁) (hout : tab.heatOutEnclosure T₁ T₄ = some J₂)
    (hw : tab.netWorkEnclosure T₁ T₂ T₃ T₄ = some J₃) :
    J₁.Encloses (braytonLossyHeatIn T₁ T₃ rp R cp ηc) ∧
      J₂.Encloses (braytonLossyHeatOut T₁ T₃ rp R cp ηt) ∧
      J₃.Encloses (braytonLossyNetWork T₁ T₃ rp R cp ηc ηt) := by
  obtain ⟨h1, -⟩ := PropertyTable.heatInEnclosure_encloses htab hin
  obtain ⟨h2, -⟩ := PropertyTable.heatOutEnclosure_encloses htab hout
  obtain ⟨h3, -⟩ := PropertyTable.netWorkEnclosure_encloses htab hw
  refine ⟨?_, ?_, ?_⟩
  · convert h1 using 1
    simp only [braytonLossyHeatIn, ← hT₂]
    ring
  · convert h2 using 1
    simp only [braytonLossyHeatOut, ← hT₄]
    ring
  · convert h3 using 1
    simp only [braytonLossyNetWork, ← hT₂, ← hT₄]
    ring

end ExergyAndLosses
