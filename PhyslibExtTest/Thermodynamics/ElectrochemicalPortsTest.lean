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
  irreversible loss of `70` W, and `Erev / Etn = 14/11 > 1`;
* the hydrogen-like inputs run as an electrolyzer at `-100` A and `7/5` V: the cell receives
  `140` W and absorbs `10` W of heat, the reversible part `-30` W plus the irreversible part
  `20` W.
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

/-- `Erev = 6/5` V for the hydrogen-like inputs. -/
private lemma reversibleVoltage_hydrogenLike : reversibleVoltage (-231564) 2 96485 = 6 / 5 := by
  unfold reversibleVoltage
  norm_num

/-- `Etn = 3/2` V for the hydrogen-like inputs. -/
private lemma thermoneutralVoltage_hydrogenLike :
    thermoneutralVoltage (-289455) 2 96485 = 3 / 2 := by
  unfold thermoneutralVoltage
  norm_num

-- Synthetic hydrogen-like inputs of the fuel-cell fixture, run as an electrolyzer: `ν = (-1, -1/2,
-- 1)` for `H2 + 1/2 O2 → H2O`, molar enthalpies `(0, 0, -289455)` J/mol, `ΔG = -231564` J/mol, `n =
-- 2` and `F = 96485` C/mol, so `Etn = 3/2` V and `Erev = 6/5` V. At `I = -100` A and `V = 7/5` V,
-- above `Erev`, the rate `-100 / 192970` mol/s, `q = 10` W and `w = 140` W satisfy the three model
-- inputs: the cell receives `140` W of electrical power and absorbs `10` W of heat (heat rejected
-- `-10` W), the reversible part `-30` W plus the irreversible part `20` W. The reversed vector has
-- the reaction enthalpy `289455` J/mol.
example :
    reversibleVoltage (-231564) 2 96485 < 7 / 5 ∧
      (-100 : ℝ) = 2 * 96485 * (-100 / 192970) ∧
      reactionEnthalpy ![0, 0, -289455] ![-1, -1 / 2, 1] * (-100 / 192970) = 10 + 140 ∧
      ProcessPorts.workOut 140 = -100 * (7 / 5 : ℝ) ∧
      -100 * (thermoneutralVoltage (-289455) 2 96485 - 7 / 5) = -10 ∧
      -100 * (thermoneutralVoltage (-289455) 2 96485 -
        reversibleVoltage (-231564) 2 96485) = -30 ∧
      -100 * (reversibleVoltage (-231564) 2 96485 - 7 / 5) = 20 ∧
      reactionEnthalpy ![0, 0, -289455] (-![-1, -1 / 2, 1]) = 289455 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold reversibleVoltage
    norm_num
  · norm_num
  · simp [reactionEnthalpy_apply, Fin.sum_univ_three]
    norm_num
  · unfold ProcessPorts.workOut
    norm_num
  · unfold thermoneutralVoltage
    norm_num
  · unfold thermoneutralVoltage reversibleVoltage
    norm_num
  · unfold reversibleVoltage
    norm_num
  · simp [reactionEnthalpy_apply, Fin.sum_univ_three]

-- Invalid after the reversal: inside the fuel-cell window, below `Erev`, a reversed current makes
-- the irreversible term negative. With the hydrogen-like `Erev = 6/5` V, `I = -100` A and `V = 1` V
-- the term `I (Erev - V)` is `-20` W.
example :
    (1 : ℝ) < reversibleVoltage (-231564) 2 96485 ∧
      -100 * (reversibleVoltage (-231564) 2 96485 - 1) = -20 := by
  refine ⟨?_, ?_⟩
  · unfold reversibleVoltage
    norm_num
  · unfold reversibleVoltage
    norm_num

-- `electricalInput_eq` at `I = -100` A and `V = 7/5` V: the port law `workOut 140 = -140` makes
-- the electrical input `w = -I V = 140` W.
example : (140 : ℝ) = -(-100) * (7 / 5) :=
  electricalInput_eq (by norm_num [ProcessPorts.workOut])

-- `sign_electricalInput_of_neg` at `I = -100` A: the input at `V = 7/5` V is positive, and at
-- `V = 0` the port law leaves no input at all.
example : SignType.sign (140 : ℝ) = 1 := by
  rw [sign_electricalInput_of_neg (I := -100) (V := 7 / 5) (by norm_num)
    (by norm_num [ProcessPorts.workOut])]
  exact sign_pos (by norm_num)

example (w : ℝ) (hport : ProcessPorts.workOut w = -100 * 0) : w = 0 := by
  have h := sign_electricalInput_of_neg (by norm_num) hport
  rwa [sign_zero, sign_eq_zero_iff] at h

-- `irreversibleHeat_nonneg_of_nonpos` includes its boundary: zero current at `V = 7/5` V, and
-- `I = -100` A at `V = Erev`.
example : 0 ≤ (0 : ℝ) * (reversibleVoltage (-231564) 2 96485 - 7 / 5) ∧
    0 ≤ (-100 : ℝ) * (reversibleVoltage (-231564) 2 96485 -
      reversibleVoltage (-231564) 2 96485) :=
  ⟨irreversibleHeat_nonneg_of_nonpos le_rfl (by rw [reversibleVoltage_hydrogenLike]; norm_num),
    irreversibleHeat_nonneg_of_nonpos (by norm_num) le_rfl⟩

-- `sign_irreversibleHeat_of_neg` at `I = -100` A: the irreversible heat is positive at `V = 7/5` V,
-- zero at `V = Erev = 6/5` V and negative at `V = 1` V, inside the fuel-cell window.
example : SignType.sign ((-100 : ℝ) * (reversibleVoltage (-231564) 2 96485 - 7 / 5)) = 1 ∧
    SignType.sign ((-100 : ℝ) * (reversibleVoltage (-231564) 2 96485 - 6 / 5)) = 0 ∧
    SignType.sign ((-100 : ℝ) * (reversibleVoltage (-231564) 2 96485 - 1)) = -1 := by
  rw [sign_irreversibleHeat_of_neg (I := -100) (by norm_num),
    sign_irreversibleHeat_of_neg (I := -100) (by norm_num),
    sign_irreversibleHeat_of_neg (I := -100) (by norm_num), reversibleVoltage_hydrogenLike]
  refine ⟨sign_pos (by norm_num), ?_, sign_neg (by norm_num)⟩
  rw [sub_self, sign_zero]

-- `sign_reversibleHeat_of_neg` at `I = -100` A: the reversible heat is absorbed (sign `-1`) for the
-- hydrogen-like inputs, where `ΔH < ΔG`, and released (sign `1`) for the entropy-gain inputs, where
-- `ΔG < ΔH`.
example :
    SignType.sign ((-100 : ℝ) * (thermoneutralVoltage (-289455) 2 96485 -
        reversibleVoltage (-231564) 2 96485)) = -1 ∧
      SignType.sign ((-100 : ℝ) * (thermoneutralVoltage (-212267) 2 96485 -
        reversibleVoltage (-270158) 2 96485)) = 1 := by
  rw [sign_reversibleHeat_of_neg (by norm_num) (by norm_num) (by norm_num),
    sign_reversibleHeat_of_neg (by norm_num) (by norm_num) (by norm_num)]
  exact ⟨sign_neg (by norm_num), sign_pos (by norm_num)⟩

-- `sign_heatReleased_of_neg` at `I = -100` A with the hydrogen-like enthalpy: at the thermoneutral
-- voltage `V = Etn = 3/2` V every heat and work meeting the model inputs have `q = 0`, and at
-- `V = 8/5` V the cell rejects heat.
example (q w : ℝ) (hbal : (-289455 : ℝ) * (-100 / 192970) = q + w)
    (hport : ProcessPorts.workOut w = -100 * (3 / 2)) : q = 0 := by
  have h := sign_heatReleased_of_neg (n := 2) (F := 96485) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbal hport
  rwa [thermoneutralVoltage_hydrogenLike, sub_self, sign_zero, sign_eq_zero_iff,
    neg_eq_zero] at h

example (q w : ℝ) (hbal : (-289455 : ℝ) * (-100 / 192970) = q + w)
    (hport : ProcessPorts.workOut w = -100 * (8 / 5)) : q < 0 := by
  have h := sign_heatReleased_of_neg (n := 2) (F := 96485) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hbal hport
  rw [thermoneutralVoltage_hydrogenLike, sign_pos (by norm_num : (0 : ℝ) < 8 / 5 - 3 / 2),
    sign_eq_one_iff] at h
  linarith

-- `sign_speciesRate` with `n = 2` and `F = 96485` C/mol: at `I = -100` A hydrogen (coefficient
-- `-1`) changes at a positive rate and water (coefficient `1`) at a negative one; at zero current
-- the rate vanishes.
example : SignType.sign ((![-1, -1 / 2, 1] : Fin 3 → ℝ) 0 * (-100 / 192970)) = 1 ∧
    SignType.sign ((![-1, -1 / 2, 1] : Fin 3 → ℝ) 2 * (-100 / 192970)) = -1 ∧
    SignType.sign ((![-1, -1 / 2, 1] : Fin 3 → ℝ) 2 * 0) = 0 := by
  rw [sign_speciesRate (n := 2) (F := 96485) (I := -100) (by norm_num) (by norm_num)
      (by norm_num),
    sign_speciesRate (n := 2) (F := 96485) (I := -100) (by norm_num) (by norm_num)
      (by norm_num),
    sign_speciesRate (n := 2) (F := 96485) (I := 0) (by norm_num) (by norm_num) (by norm_num)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    sign_zero, mul_zero]
  rw [sign_neg (by norm_num : (-1 : ℝ) < 0), sign_neg (by norm_num : (-100 : ℝ) < 0),
    sign_pos (by norm_num : (0 : ℝ) < 1)]
  decide

-- `electrolyzer_accounting` at the hydrogen-like electrolyzer inputs (`I = -100` A, `V = 7/5` V,
-- `r = -100/192970` mol/s, `q = 10` W, `w = 140` W): every hypothesis holds; the cell receives
-- `140` W, the reverse rate is positive, and hydrogen is produced at `100/192970` mol/s.
example : (140 : ℝ) = -(-100) * (7 / 5) ∧ (0 : ℝ) < 140 ∧ (0 : ℝ) < -(-100) / (2 * 96485) ∧
    (![-1, -1 / 2, 1] : Fin 3 → ℝ) 0 * (-100 / 192970) = 100 / 192970 := by
  obtain ⟨h1, h2, -, -, -, h6, h7, -⟩ := electrolyzer_accounting (H := ![0, 0, -289455])
    (ν := ![-1, -1 / 2, 1]) (ΔG := -231564) (n := 2) (F := 96485) (I := -100) (V := 7 / 5)
    (r := -100 / 192970) (q := 10) (w := 140) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [reversibleVoltage]) (by norm_num)
    (by norm_num [reactionEnthalpy_apply, Fin.sum_univ_three])
    (by norm_num [ProcessPorts.workOut])
  refine ⟨h1, h2, h6, ?_⟩
  rw [h7 0]
  norm_num

end PhyslibExtTest.Thermodynamics.ElectrochemicalPorts
