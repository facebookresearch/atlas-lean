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
# Electrochemical ports: fuel-cell accounting, electrolyzer current reversal and species direction

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

Sections C to E run the same accounting with the current reversed and the reaction orientation
kept: `ν`, `ΔG`, `ΔH`, `Erev` and `Etn` stay those of the fuel cell, and an electrolyzer is the same
cell at `I < 0`, where Faraday's law gives `r < 0`. That `V ≥ Erev` at a reversed current is a
supplied model input, as `V ≤ Erev` is for the fuel cell. With the same model inputs the work
received is the electrical input `w = -I V`; for `I < 0` it has the sign of `V`. The heat rejected
keeps its split. The irreversible part is nonnegative for `I ≤ 0` and `V ≥ Erev`; for `I < 0` it
has the sign of `V - Erev`, so the fuel-cell window `V ≤ Erev` is not retained after the reversal.
For `n, F > 0` and `I < 0` the reversible part has the sign of `ΔH - ΔG`, opposite to the fuel
cell, and the heat rejected has the sign of `V - Etn`: the cell absorbs heat below the
thermoneutral voltage, rejects heat above it, and exchanges none at `V = Etn`.

For `n, F > 0`, species `i` changes at the rate `ν i * r`, of sign `sign (ν i) * sign I`. At
`I < 0` the reversed vector `-ν` runs at the positive rate `-I / (n F)` and has the reaction
enthalpy `-ΔH`. Which positive extents of `-ν` an inventory allows is a stoichiometry question,
answered by the reversed-vector results of `PhyslibExt.Chemistry.Stoichiometry.Extent`.

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
- `ElectrochemicalPorts.electricalInput_eq`: at any current the work received is `w = -I V`.
- `ElectrochemicalPorts.irreversibleHeat_nonneg_of_nonpos`: `0 ≤ I (Erev - V)` for `I ≤ 0` and
  `V ≥ Erev`.
- `ElectrochemicalPorts.sign_heatReleased_of_neg`: for `n, F > 0` and `I < 0` the heat rejected has
  the sign of `V - Etn`.
- `ElectrochemicalPorts.electrolyzer_accounting`: the combined power, heat and species statement
  with `ΔH = reactionEnthalpy H ν` and `I < 0`.

## iii. Table of contents

- A. Reversible and thermoneutral voltages
- B. Heat accounting
- C. Electrical input and heat under a reversed current
- D. Species direction
- E. Electrolyzer accounting

## iv. References

- J. Larminie and A. Dicks, *Fuel Cell Systems Explained*, Wiley: the reversible voltage
  `-Δg_f / (2F)` of the hydrogen cell, the efficiency limit `Δg_f / Δh_f`, and the cell heat
  production in terms of the cell voltage.
- A. J. Bard and L. R. Faulkner, *Electrochemical Methods*, ch. 1-2: galvanic and electrolytic
  cells, Faraday's law and `ΔG = -n F E`.
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

/-! ## C. Electrical input and heat under a reversed current -/

/-- Electrical input under the port law `W_out = I V`: the work received by the cell is
`w = -I V`, for every current and voltage. At a reversed current `I < 0` it is the power `|I| V`
fed to the electrolyzer. -/
lemma electricalInput_eq {I V w : ℝ} (hport : ProcessPorts.workOut w = I * V) : w = -I * V := by
  unfold ProcessPorts.workOut at hport
  linarith

/-- Sign of the electrical input: at a reversed current `I < 0` the work received `w` has the sign
of `V`, so it is an input exactly when `V > 0` and vanishes at `V = 0`. -/
lemma sign_electricalInput_of_neg {I V w : ℝ} (hI : I < 0)
    (hport : ProcessPorts.workOut w = I * V) : SignType.sign w = SignType.sign V := by
  rw [electricalInput_eq hport, sign_mul, sign_pos (neg_pos.mpr hI), one_mul]

/-- The irreversible heat `I * (Erev - V)` is nonnegative for a current `I ≤ 0` at a terminal
voltage `V ≥ Erev`, zero current and `V = Erev` included. -/
lemma irreversibleHeat_nonneg_of_nonpos {ΔG n F I V : ℝ} (hI : I ≤ 0)
    (hV : reversibleVoltage ΔG n F ≤ V) : 0 ≤ I * (reversibleVoltage ΔG n F - V) := by
  exact mul_nonneg_of_nonpos_of_nonpos hI (sub_nonpos.mpr hV)

/-- Sign of the irreversible heat at a reversed current `I < 0`: `I * (Erev - V)` has the sign of
`V - Erev`. It is positive above `Erev`, zero at `V = Erev`, and negative below `Erev`, inside the
fuel-cell window, which is therefore not retained after the reversal. -/
lemma sign_irreversibleHeat_of_neg {ΔG n F I V : ℝ} (hI : I < 0) :
    SignType.sign (I * (reversibleVoltage ΔG n F - V)) =
      SignType.sign (V - reversibleVoltage ΔG n F) := by
  rw [sign_mul, sign_neg hI, show V - reversibleVoltage ΔG n F =
    -(reversibleVoltage ΔG n F - V) by ring, Left.sign_neg, neg_one_mul]

/-- Sign of the reversible heat at a reversed current: for `n, F > 0` and `I < 0` the reversible
part `I * (Etn - Erev)` of the heat rejected has the sign of `ΔH - ΔG`, opposite to the fuel cell,
so it is absorbed when `ΔH < ΔG` and released when `ΔG < ΔH`. -/
lemma sign_reversibleHeat_of_neg {ΔG ΔH n F I : ℝ} (hn : 0 < n) (hF : 0 < F) (hI : I < 0) :
    SignType.sign (I * (thermoneutralVoltage ΔH n F - reversibleVoltage ΔG n F)) =
      SignType.sign (ΔH - ΔG) := by
  rw [sign_mul, sign_neg hI, sign_thermoneutralVoltage_sub_reversibleVoltage hn hF,
    show ΔH - ΔG = -(ΔG - ΔH) by ring, Left.sign_neg, neg_one_mul]

/-- Heat direction at a reversed current: with the model inputs of `heatReleased_eq`, `n, F > 0`
and `I < 0`, the heat rejected `-q` has the sign of `V - Etn`. The cell absorbs heat below the
thermoneutral voltage, rejects heat above it, and `q = 0` at `V = Etn`. -/
lemma sign_heatReleased_of_neg {ΔH n F I V r q w : ℝ} (hn : 0 < n) (hF : 0 < F) (hI : I < 0)
    (hFaraday : I = n * F * r) (hbal : ΔH * r = q + w) (hport : ProcessPorts.workOut w = I * V) :
    SignType.sign (-q) = SignType.sign (V - thermoneutralVoltage ΔH n F) := by
  obtain ⟨h, -⟩ := heatReleased_eq (ΔG := 0) hn hF hFaraday hbal hport
  rw [h, sign_mul, sign_neg hI, show V - thermoneutralVoltage ΔH n F =
    -(thermoneutralVoltage ΔH n F - V) by ring, Left.sign_neg, neg_one_mul]

/-! ## D. Species direction -/

/-- Species direction: with Faraday's law `I = n F r` and `n, F > 0`, the rate `ν i * r` at which
species `i` changes has the sign `sign (ν i) * sign I`. At `I < 0` every species with a nonzero
coefficient moves against it, along the reversed vector `-ν`; at `I = 0` no species changes. -/
lemma sign_speciesRate {ι : Type*} {ν : ι → ℝ} {n F I r : ℝ} (hn : 0 < n) (hF : 0 < F)
    (hFaraday : I = n * F * r) (i : ι) :
    SignType.sign (ν i * r) = SignType.sign (ν i) * SignType.sign I := by
  subst hFaraday
  simp only [sign_mul, sign_pos hn, sign_pos hF, one_mul]

/-! ## E. Electrolyzer accounting -/

/-- Electrolyzer accounting for a reaction `ν` with molar enthalpies `H`, in the fuel-cell
orientation, so `Δ_r H = reactionEnthalpy H ν`: with `ΔG < 0`, `n, F > 0`, a reversed current
`I < 0`, a terminal voltage `V ≥ Erev` and the model inputs of `heatReleased_eq`, the cell receives
the electrical power `w = -I V > 0`; the heat rejected is `I (Etn - V)`, the reversible plus the
irreversible part, and the irreversible part is nonnegative; the reversed vector `-ν` runs at the
positive rate `-I / (n F)`, every species rate `ν i * r` equals `(-ν) i * (-I / (n F))`, and the
enthalpy balance reads `Δ_r H (-ν) * (-I / (n F)) = q + w`. -/
lemma electrolyzer_accounting {ι : Type*} [Fintype ι] {H ν : ι → ℝ} {ΔG n F I V r q w : ℝ}
    (hΔG : ΔG < 0) (hn : 0 < n) (hF : 0 < F) (hI : I < 0) (hV : reversibleVoltage ΔG n F ≤ V)
    (hFaraday : I = n * F * r) (hbal : reactionEnthalpy H ν * r = q + w)
    (hport : ProcessPorts.workOut w = I * V) :
    w = -I * V ∧ 0 < w ∧
      -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - V) ∧
      -q = I * (thermoneutralVoltage (reactionEnthalpy H ν) n F - reversibleVoltage ΔG n F) +
        I * (reversibleVoltage ΔG n F - V) ∧
      0 ≤ I * (reversibleVoltage ΔG n F - V) ∧
      0 < -I / (n * F) ∧ (∀ i, ν i * r = (-ν) i * (-I / (n * F))) ∧
      reactionEnthalpy H (-ν) * (-I / (n * F)) = q + w := by
  have hNF : 0 < n * F := mul_pos hn hF
  have hw : w = -I * V := electricalInput_eq hport
  have hErev : 0 < reversibleVoltage ΔG n F := reversibleVoltage_pos hΔG hn hF
  have hheat := heatReleased_eq (ΔG := ΔG) hn hF hFaraday hbal hport
  have hr : r = I / (n * F) := by
    rw [hFaraday, mul_div_cancel_left₀ r hNF.ne']
  refine ⟨hw, ?_, hheat.1, hheat.2, irreversibleHeat_nonneg_of_nonpos hI.le hV, ?_, ?_, ?_⟩
  · rw [hw]
    exact mul_pos (neg_pos.mpr hI) (lt_of_lt_of_le hErev hV)
  · exact div_pos (neg_pos.mpr hI) hNF
  · intro i
    rw [hr, Pi.neg_apply]
    ring
  · rw [map_neg, ← hbal, hr]
    ring

end ElectrochemicalPorts
