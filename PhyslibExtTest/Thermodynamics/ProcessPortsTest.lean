/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.UnitsOrScaling
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Thermodynamics.ProcessPorts`

One kilogram of air, `Rs = 287 J/(kg K)`, at `300 K`, expanding from `0.5 m³` to `1 m³`:

* the work out is `86100 log 2 J > 0`, while the IUPAC work done on the gas is negative;
* against the final pressure `86100 Pa` the expansion does `43050 J`, strictly less than the
  reversible work;
* Celsius readings are not absolute temperatures inside logarithms.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.ProcessPorts

open _root_.Chemistry.Thermodynamics _root_.ProcessPorts

-- Nonzero isothermal expansion: `W_out = 86100 log 2 J > 0`, while the IUPAC work done on the
-- gas is negative.
example :
    workOut (isothermalWorkOn 1 287 300 0.5 1) = 86100 * Real.log 2 ∧
      0 < workOut (isothermalWorkOn 1 287 300 0.5 1) ∧ isothermalWorkOn 1 287 300 0.5 1 < 0 := by
  have h2 : (1 : ℝ) / 0.5 = 2 := by norm_num
  have hnum : (1 : ℝ) * 287 * 300 = 86100 := by norm_num
  have hW : workOut (isothermalWorkOn 1 287 300 0.5 1) = 86100 * Real.log 2 := by
    simp only [workOut, isothermalWorkOn, neg_neg]
    rw [h2, hnum]
  have hW' : isothermalWorkOn 1 287 300 0.5 1 = -(86100 * Real.log 2) := by
    simp only [isothermalWorkOn]
    rw [h2, hnum]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : 0 < (86100 : ℝ) * Real.log 2 := mul_pos (by norm_num) hlog
  refine ⟨hW, ?_, ?_⟩
  · rw [hW]
    exact hpos
  · rw [hW']
    exact neg_neg_of_pos hpos

-- Against the final pressure `p_ext = 86100 Pa` the same expansion does `43050 J`, strictly
-- less than the reversible `86100 log 2 J`.
example :
    workOut (irreversibleWorkOn 86100 0.5 1) = 43050 ∧
      workOut (irreversibleWorkOn 86100 0.5 1) < workOut (isothermalWorkOn 1 287 300 0.5 1) := by
  have hirr : workOut (irreversibleWorkOn 86100 0.5 1) = 43050 := by
    simp only [workOut, irreversibleWorkOn, neg_neg]
    norm_num
  have hW : workOut (isothermalWorkOn 1 287 300 0.5 1) = 86100 * Real.log 2 := by
    have h2 : (1 : ℝ) / 0.5 = 2 := by norm_num
    have hnum : (1 : ℝ) * 287 * 300 = 86100 := by norm_num
    simp only [workOut, isothermalWorkOn, neg_neg]
    rw [h2, hnum]
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≠ 1 by norm_num)
    have h2 : Real.log (2 : ℝ) = -Real.log (1 / 2) := by
      have e : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
      rw [e, Real.log_inv, neg_neg]
    linarith
  refine ⟨hirr, ?_⟩
  rw [hirr, hW]
  have e : (43050 : ℝ) = 86100 * (1 / 2) := by norm_num
  rw [e]
  exact mul_lt_mul_of_pos_left hlog2 (by norm_num)

-- Celsius readings are not absolute temperatures inside logarithms: for `20 °C` and `40 °C`
-- the log ratio of the Celsius numbers differs from that of the absolute temperatures.
example :
    Real.log (40 / 20) ≠
      Real.log (EarthScience.celsiusToKelvin 40 / EarthScience.celsiusToKelvin 20) := by
  have h1 : (40 : ℝ) / 20 = 2 := by norm_num
  have h2 : EarthScience.celsiusToKelvin 40 / EarthScience.celsiusToKelvin 20
      = 313.15 / 293.15 := by
    simp only [EarthScience.celsiusToKelvin]
    norm_num
  rw [h1, h2]
  have hne : (2 : ℝ) ≠ 313.15 / 293.15 := by norm_num
  intro hcon
  apply hne
  have hpos1 : (0 : ℝ) < 2 := by norm_num
  have hpos2 : (0 : ℝ) < 313.15 / 293.15 := by norm_num
  have hcon' := congrArg Real.exp hcon
  rw [Real.exp_log hpos1, Real.exp_log hpos2] at hcon'
  exact hcon'

end PhyslibExtTest.Thermodynamics.ProcessPorts
