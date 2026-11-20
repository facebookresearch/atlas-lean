/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.Thermodynamics.GasCycles
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exergy and losses: exergy destruction and nonideal Brayton losses

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

## iii. Table of contents

- A. Balances with matched ports
- B. Exergy destruction
- C. Nonideal Brayton cycle
  - C.1. States
  - C.2. Work and heat
  - C.3. The positive-work threshold
  - C.4. Monotonicity in the component efficiencies

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

end ExergyAndLosses
