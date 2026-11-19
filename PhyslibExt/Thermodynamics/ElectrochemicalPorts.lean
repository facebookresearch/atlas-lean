/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Sign.Defs
public import PhyslibExt.Chemistry.Thermodynamics.Thermochemistry
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Electrochemical ports: fuel-cell chemical, electrical and heat accounting

## i. Overview

One reaction orientation of an operating fuel cell, per mole of reaction as written: the reaction
enthalpy `ΔH` (in the main result `reactionEnthalpy H ν`, products positive), a supplied reaction
Gibbs energy `ΔG` at the cell temperature and pressure, `n > 0` electrons per mole of reaction and
the Faraday constant `F > 0`. The reversible voltage is `Erev = -ΔG / (n F)` and the thermoneutral
voltage `Etn = -ΔH / (n F)`; for `n, F > 0` both are positive when `ΔG, ΔH < 0`, and the gap
`Etn - Erev = (ΔG - ΔH) / (n F)` has the sign of `ΔG - ΔH`. That `-ΔG` is the reversible
electrical work, so that `V ≤ Erev`, is a supplied model input, not derived here; no cell
potential is derived from composition (no Nernst law).

The cell runs at current `I ≥ 0` and terminal voltage `0 ≤ V ≤ Erev`. Model inputs: Faraday's law
`I = n F r` for the reaction rate `r`, the isothermal enthalpy balance `ΔH r = q + w` with heat `q`
and work `w` received by the cell (the IUPAC signs of `ΔU = q + w`), and the electrical port law
`W_out = I V` for the power delivered at the terminals, with `W_out = -w` the work-out adapter of
the process ports. Then the heat rejected is `-q = I (Etn - V)`, which splits into the reversible
part `I (Etn - Erev)` and the irreversible part `I (Erev - V)`, nonnegative for `I ≥ 0` and
`V ≤ Erev`; for an exothermic reaction (`ΔH < 0`) the voltage efficiency satisfies
`0 ≤ V / Etn ≤ Erev / Etn`. For a positive current `I > 0` the reversible part has the sign of
`ΔG - ΔH` (at `I = 0` it vanishes), which can be negative, and `Erev / Etn` can exceed `1`:
without entropy assumptions neither `I (Etn - Erev) ≥ 0` nor `Erev / Etn ≤ 1` follows.

## ii. Key results

- `ElectrochemicalPorts.heatReleased_eq`: the heat rejected is `I (Etn - V)` and its split.
- `ElectrochemicalPorts.sign_reversibleHeat`: for `n, F > 0` and `I > 0` the reversible part has
  the sign of `ΔG - ΔH`.
- `ElectrochemicalPorts.irreversibleHeat_nonneg`: the irreversible part is nonnegative for
  `I ≥ 0` and `V ≤ Erev`.
- `ElectrochemicalPorts.voltageRatio_le`: `V / Etn ≤ Erev / Etn` for `ΔH < 0`, `n, F > 0` and
  `V ≤ Erev`.
- `ElectrochemicalPorts.fuelCell_heat_accounting`: the combined statement with
  `ΔH = reactionEnthalpy H ν`.

## iii. Table of contents

- A. Reversible and thermoneutral voltages
- B. Heat accounting

## iv. References

- J. Larminie and A. Dicks, *Fuel Cell Systems Explained*, Wiley: the reversible voltage
  `-Δg_f / (2F)` of the hydrogen cell, the efficiency limit `Δg_f / Δh_f`, and the cell heat
  production in terms of the cell voltage.
- A. J. Bard and L. R. Faulkner, *Electrochemical Methods*, ch. 2: `ΔG = -n F E`.
- E. R. Cohen et al., *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book),
  3rd ed., 2007: `ΔU = q + w` with `w` the work done on the system.
- `PhyslibExt.Thermodynamics.ProcessPorts` (`workOut`) and
  `PhyslibExt.Chemistry.Thermodynamics.Thermochemistry` (`reactionEnthalpy`).
-/

@[expose] public section

namespace ElectrochemicalPorts

open Chemistry.Thermodynamics

/-! ## A. Reversible and thermoneutral voltages -/

/-- Reversible voltage `Erev = -ΔG / (n F)` from a supplied reaction Gibbs energy `ΔG` per mole
of reaction as written (at the cell temperature, pressure and composition), `n` electrons per
mole of reaction and the Faraday constant `F`. -/
noncomputable def reversibleVoltage (ΔG n F : ℝ) : ℝ :=
  -ΔG / (n * F)

/-- Thermoneutral voltage `Etn = -ΔH / (n F)` from the reaction enthalpy `ΔH` per mole of
reaction as written. -/
noncomputable def thermoneutralVoltage (ΔH n F : ℝ) : ℝ :=
  -ΔH / (n * F)

/-- For `n, F > 0`, a spontaneous reaction, `ΔG < 0`, has a positive reversible voltage. -/
lemma reversibleVoltage_pos {ΔG n F : ℝ} (hΔG : ΔG < 0) (hn : 0 < n) (hF : 0 < F) :
    0 < reversibleVoltage ΔG n F := by
  unfold reversibleVoltage
  exact div_pos (by linarith) (mul_pos hn hF)

/-- For `n, F > 0`, an exothermic reaction, `ΔH < 0`, has a positive thermoneutral voltage. -/
lemma thermoneutralVoltage_pos {ΔH n F : ℝ} (hΔH : ΔH < 0) (hn : 0 < n) (hF : 0 < F) :
    0 < thermoneutralVoltage ΔH n F := by
  unfold thermoneutralVoltage
  exact div_pos (by linarith) (mul_pos hn hF)

/-- The gap between the two voltages is `Etn - Erev = (ΔG - ΔH) / (n F)`, for all inputs. For
`n, F > 0` it has the sign of `ΔG - ΔH` (`sign_thermoneutralVoltage_sub_reversibleVoltage`). -/
lemma thermoneutralVoltage_sub_reversibleVoltage (ΔG ΔH n F : ℝ) :
    thermoneutralVoltage ΔH n F - reversibleVoltage ΔG n F = (ΔG - ΔH) / (n * F) := by
  unfold thermoneutralVoltage reversibleVoltage
  ring

/-- Sign of the voltage gap: for `n, F > 0`, `Etn - Erev` has the sign of `ΔG - ΔH`, so the
reversible heat per unit current is released, zero or absorbed as `ΔH < ΔG`, `ΔG = ΔH` or
`ΔG < ΔH`; the supplied data may make it either sign. -/
lemma sign_thermoneutralVoltage_sub_reversibleVoltage {ΔG ΔH n F : ℝ} (hn : 0 < n) (hF : 0 < F) :
    SignType.sign (thermoneutralVoltage ΔH n F - reversibleVoltage ΔG n F) =
      SignType.sign (ΔG - ΔH) := by
  rw [thermoneutralVoltage_sub_reversibleVoltage, div_eq_mul_inv, sign_mul,
    sign_pos (inv_pos.mpr (mul_pos hn hF)), mul_one]

/-! ## B. Heat accounting -/

/-- Heat rejected by an operating cell. Model inputs: Faraday's law `I = n F r` for the reaction
rate `r` (moles of reaction per second), the isothermal enthalpy balance `ΔH r = q + w` with the
heat `q` and work `w` received by the cell per second, and the port law `W_out = I V` for the
electrical power delivered at the terminals. Then the heat rejected per second is
`-q = I * (Etn - V)`, the reversible part `I * (Etn - Erev)` plus the irreversible part
`I * (Erev - V)`. -/
lemma heatReleased_eq {ΔG ΔH n F I V r q w : ℝ} (hn : 0 < n) (hF : 0 < F)
    (hFaraday : I = n * F * r) (hbal : ΔH * r = q + w) (hport : ProcessPorts.workOut w = I * V) :
    -q = I * (thermoneutralVoltage ΔH n F - V) ∧
      -q = I * (thermoneutralVoltage ΔH n F - reversibleVoltage ΔG n F) +
        I * (reversibleVoltage ΔG n F - V) := by
  have hNF : n * F ≠ 0 := ne_of_gt (mul_pos hn hF)
  have hport' : -w = I * V := hport
  have hE : I * thermoneutralVoltage ΔH n F = -ΔH * r := by
    unfold thermoneutralVoltage
    rw [hFaraday]
    field_simp
  have hmain : -q = I * (thermoneutralVoltage ΔH n F - V) := by
    rw [mul_sub, hE]
    linear_combination hbal - hport'
  exact ⟨hmain, by linear_combination hmain⟩

/-- Sign of the reversible heat: for `n, F > 0` and a current `I > 0`, the reversible part
`I * (Etn - Erev)` of the heat rejected has the sign of `ΔG - ΔH`, so it is released when
`ΔH < ΔG` and absorbed when `ΔG < ΔH`. At `I = 0` it vanishes. -/
lemma sign_reversibleHeat {ΔG ΔH n F I : ℝ} (hn : 0 < n) (hF : 0 < F) (hI : 0 < I) :
    SignType.sign (I * (thermoneutralVoltage ΔH n F - reversibleVoltage ΔG n F)) =
      SignType.sign (ΔG - ΔH) := by
  rw [sign_mul, sign_pos hI, one_mul, sign_thermoneutralVoltage_sub_reversibleVoltage hn hF]

/-- The irreversible heat `I * (Erev - V)` is nonnegative for a current `I ≥ 0` at a terminal
voltage `V ≤ Erev`. -/
lemma irreversibleHeat_nonneg {ΔG n F I V : ℝ} (hI : 0 ≤ I) (hV : V ≤ reversibleVoltage ΔG n F) :
    0 ≤ I * (reversibleVoltage ΔG n F - V) := by
  exact mul_nonneg hI (by linarith)

/-- Voltage efficiency bound: for an exothermic reaction, `n, F > 0` and `V ≤ Erev`, the ratio
`V / Etn` is at most `Erev / Etn`. The bound `Erev / Etn` itself may exceed `1`. -/
lemma voltageRatio_le {ΔG ΔH n F V : ℝ} (hΔH : ΔH < 0) (hn : 0 < n) (hF : 0 < F)
    (hV : V ≤ reversibleVoltage ΔG n F) :
    V / thermoneutralVoltage ΔH n F ≤ reversibleVoltage ΔG n F / thermoneutralVoltage ΔH n F := by
  have hE : 0 < thermoneutralVoltage ΔH n F := thermoneutralVoltage_pos hΔH hn hF
  have hEi : 0 ≤ (thermoneutralVoltage ΔH n F)⁻¹ := inv_nonneg.mpr (le_of_lt hE)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hV hEi

/-- Fuel-cell heat accounting for a reaction `ν` with molar enthalpies `H`, so
`Δ_r H = reactionEnthalpy H ν`: with `Δ_r H < 0`, `n, F > 0`, a current `I ≥ 0` and a terminal
voltage `0 ≤ V ≤ Erev`, the model inputs of `heatReleased_eq` give the heat rejected
`I * (Etn - V)`, its reversible and irreversible parts, a nonnegative irreversible part and the
voltage efficiency `0 ≤ V / Etn ≤ Erev / Etn`. -/
lemma fuelCell_heat_accounting {ι : Type*} [Fintype ι] {H ν : ι → ℝ} {ΔG n F I V r q w : ℝ}
    (hΔH : reactionEnthalpy H ν < 0) (hn : 0 < n) (hF : 0 < F) (hI : 0 ≤ I) (hV₀ : 0 ≤ V)
    (hV : V ≤ reversibleVoltage ΔG n F) (hFaraday : I = n * F * r)
    (hbal : reactionEnthalpy H ν * r = q + w) (hport : ProcessPorts.workOut w = I * V) :
    -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - V) ∧
      -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - reversibleVoltage ΔG n F) +
        I * (reversibleVoltage ΔG n F - V) ∧
      0 ≤ I * (reversibleVoltage ΔG n F - V) ∧
      0 ≤ V / thermoneutralVoltage (reactionEnthalpy H ν) n F ∧
      V / thermoneutralVoltage (reactionEnthalpy H ν) n F ≤
        reversibleVoltage ΔG n F / thermoneutralVoltage (reactionEnthalpy H ν) n F := by
  have hE : 0 < thermoneutralVoltage (reactionEnthalpy H ν) n F :=
    thermoneutralVoltage_pos hΔH hn hF
  have hheat : -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - V) ∧
      -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - reversibleVoltage ΔG n F) +
        I * (reversibleVoltage ΔG n F - V) :=
    heatReleased_eq hn hF hFaraday hbal hport
  have hirr := irreversibleHeat_nonneg hI hV
  have hle := voltageRatio_le hΔH hn hF hV
  have hnonneg : 0 ≤ V / thermoneutralVoltage (reactionEnthalpy H ν) n F :=
    div_nonneg hV₀ (le_of_lt hE)
  exact ⟨hheat.1, hheat.2, hirr, hnonneg, hle⟩

end ElectrochemicalPorts
