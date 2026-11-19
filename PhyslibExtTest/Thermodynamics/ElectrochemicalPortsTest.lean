/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Thermodynamics.ElectrochemicalPorts

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Thermodynamics.ElectrochemicalPorts`

Synthetic inputs, not property data, with `n = 2` and `F = 96485` C/mol:

* near the hydrogen cell (`ΔH = -289455` J/mol from the reaction enthalpy, `ΔG = -231564` J/mol):
  `Etn = 3/2` V and `Erev = 6/5` V; at `100` A and `0.7` V the three model inputs hold and the
  heat rejected, `80` W, is `30` W reversible plus `50` W irreversible;
* a reaction that gains entropy (`ΔG = -270158 < ΔH = -212267` J/mol): `Erev = 7/5` V exceeds
  `Etn = 11/10` V, the reversible heat `-30` W is absorbed, the heat rejected is `40` W against an
  irreversible loss of `70` W, and `Erev / Etn = 14/11 > 1`.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.ElectrochemicalPorts

open _root_.Chemistry.Thermodynamics _root_.ElectrochemicalPorts

-- Synthetic inputs near the hydrogen cell (`H2 + 1/2 O2 → H2O`, liquid water): `ν = (-1, -1/2,
-- 1)`, molar enthalpies `(0, 0, -289455)` J/mol, `ΔG = -231564` J/mol, `n = 2`, `F = 96485` C/mol,
-- so `Etn = 3/2` V and `Erev = 6/5` V. At `I = 100` A and `V = 7/10` V the reaction rate
-- `100 / 192970` mol/s, `q = -80` W and `w = -70` W satisfy the three model inputs, and the heat
-- rejected, `80` W, is the reversible part `30` W plus the irreversible part `50` W.
example :
    reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1] = -289455 ∧
      thermoneutralVoltage (-289455) 2 96485 = 3 / 2 ∧
      reversibleVoltage (-231564) 2 96485 = 6 / 5 ∧
      (100 : ℝ) = 2 * 96485 * (100 / 192970) ∧
      reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1] * (100 / 192970) = -80 + -70 ∧
      ProcessPorts.workOut (-70) = 100 * (7 / 10 : ℝ) ∧
      100 * (thermoneutralVoltage (-289455) 2 96485 - reversibleVoltage (-231564) 2 96485) = 30 ∧
      100 * (reversibleVoltage (-231564) 2 96485 - 7 / 10) = 50 := by
  have hΔH : reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1] = -289455 := by
    simp [reactionEnthalpy_apply, Fin.sum_univ_three]
  have hEtn : thermoneutralVoltage (-289455) 2 96485 = 3 / 2 := by
    unfold thermoneutralVoltage
    norm_num
  have hErev : reversibleVoltage (-231564) 2 96485 = 6 / 5 := by
    unfold reversibleVoltage
    norm_num
  refine ⟨hΔH, hEtn, hErev, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rw [hΔH]
    norm_num
  · unfold ProcessPorts.workOut
    norm_num
  · rw [hEtn, hErev]
    norm_num
  · rw [hErev]
    norm_num

-- Synthetic inputs with `ΔG < ΔH` (a reaction that gains entropy): `ΔG = -270158` J/mol,
-- `ΔH = -212267` J/mol, `n = 2`, `F = 96485` C/mol, so `Erev = 7/5` V and `Etn = 11/10` V. At
-- `I = 100` A and `V = 7/10` V the heat rejected is `40` W, the reversible part is `-30` W
-- (absorbed) and the irreversible part is `70` W, and `Erev / Etn = 14/11 > 1`.
example :
    reversibleVoltage (-270158) 2 96485 = 7 / 5 ∧
      thermoneutralVoltage (-212267) 2 96485 = 11 / 10 ∧
      100 * (thermoneutralVoltage (-212267) 2 96485 - 7 / 10) = 40 ∧
      100 * (thermoneutralVoltage (-212267) 2 96485 - reversibleVoltage (-270158) 2 96485) = -30 ∧
      100 * (reversibleVoltage (-270158) 2 96485 - 7 / 10) = 70 ∧
      1 < reversibleVoltage (-270158) 2 96485 / thermoneutralVoltage (-212267) 2 96485 := by
  have hErev : reversibleVoltage (-270158) 2 96485 = 7 / 5 := by
    unfold reversibleVoltage
    norm_num
  have hEtn : thermoneutralVoltage (-212267) 2 96485 = 11 / 10 := by
    unfold thermoneutralVoltage
    norm_num
  refine ⟨hErev, hEtn, ?_, ?_, ?_, ?_⟩
  · rw [hEtn]
    norm_num
  · rw [hEtn, hErev]
    norm_num
  · rw [hErev]
    norm_num
  · rw [hErev, hEtn]
    norm_num

-- The combined statement on the hydrogen-like inputs: all nine hypotheses hold, so the heat
-- rejected `-q = 80` W is `I (Etn - V)`, and the voltage efficiency `V / Etn = 7/15` is at most
-- `Erev / Etn = 4/5`.
example :
    (80 : ℝ) = 100 * (thermoneutralVoltage (reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1]) 2
        96485 - 7 / 10) ∧
      (7 / 10 : ℝ) / thermoneutralVoltage (reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1]) 2
          96485 ≤
        reversibleVoltage (-231564) 2 96485 /
          thermoneutralVoltage (reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1]) 2 96485 := by
  obtain ⟨h1, -, -, -, h5⟩ := fuelCell_heat_accounting (H := ![0, 0, -289455])
    (ν := ![-1, -1 / 2, 1]) (ΔG := -231564) (n := 2) (F := 96485) (I := 100) (V := 7 / 10)
    (r := 100 / 192970) (q := -80) (w := -70)
    (by norm_num [reactionEnthalpy_apply, Fin.sum_univ_three]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [reversibleVoltage]) (by norm_num)
    (by norm_num [reactionEnthalpy_apply, Fin.sum_univ_three])
    (by norm_num [ProcessPorts.workOut])
  exact ⟨by linarith, h5⟩

-- `heatReleased_eq` on the entropy-gain inputs at `I = 100` A and `V = 7/10` V, with
-- `r = 100 / 192970` mol/s, `q = -40` W and `w = -70` W: the heat rejected, `40` W, is the
-- reversible part plus the irreversible loss, which here is `70` W.
example :
    (40 : ℝ) = 100 * (thermoneutralVoltage (-212267) 2 96485 -
        reversibleVoltage (-270158) 2 96485) +
      100 * (reversibleVoltage (-270158) 2 96485 - 7 / 10) := by
  obtain ⟨-, h2⟩ := heatReleased_eq (ΔG := -270158) (ΔH := -212267) (n := 2) (F := 96485)
    (I := 100) (V := 7 / 10) (r := 100 / 192970) (q := -40) (w := -70) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [ProcessPorts.workOut])
  linarith

-- With `n, F > 0` the gap `Etn - Erev = (ΔG - ΔH) / (n F)` is negative when `ΔG < ΔH`: `-3/10` V
-- for the entropy-gain inputs, so the reversible heat at a positive current is absorbed.
example :
    thermoneutralVoltage (-212267) 2 96485 - reversibleVoltage (-270158) 2 96485 = -3 / 10 := by
  rw [thermoneutralVoltage_sub_reversibleVoltage]
  norm_num

-- `sign_reversibleHeat` at `n = 2`, `F = 96485` C/mol and `I = 100` A: the reversible heat is
-- released (sign `1`) for the hydrogen-like inputs, where `ΔH < ΔG`, and absorbed (sign `-1`) for
-- the entropy-gain inputs, where `ΔG < ΔH`.
example :
    SignType.sign (100 * (thermoneutralVoltage (-289455) 2 96485 -
        reversibleVoltage (-231564) 2 96485)) = 1 ∧
      SignType.sign (100 * (thermoneutralVoltage (-212267) 2 96485 -
        reversibleVoltage (-270158) 2 96485)) = -1 := by
  rw [sign_reversibleHeat (by norm_num) (by norm_num) (by norm_num),
    sign_reversibleHeat (by norm_num) (by norm_num) (by norm_num)]
  exact ⟨sign_pos (by norm_num), sign_neg (by norm_num)⟩

-- Invalid without `0 < n`: `n = -1`, `F = 1`, `ΔG = 1` and `ΔH = 0` give `ΔG - ΔH = 1` but the gap
-- `Etn - Erev = -1`, so `sign_thermoneutralVoltage_sub_reversibleVoltage` needs its hypotheses.
example :
    SignType.sign (thermoneutralVoltage 0 (-1) 1 - reversibleVoltage 1 (-1) 1) = -1 ∧
      SignType.sign ((1 : ℝ) - 0) = 1 := by
  refine ⟨sign_neg ?_, sign_pos (by norm_num)⟩
  norm_num [thermoneutralVoltage, reversibleVoltage]

end PhyslibExtTest.Thermodynamics.ElectrochemicalPorts
