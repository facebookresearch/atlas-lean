/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.UnitsOrScaling
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Thermodynamics.ProcessPorts`

One kilogram of air, `Rs = 287 J/(kg K)`, at `300 K`, expanding from `0.5 m³` to `1 m³`:

* the work out is `86100 log 2 J > 0`, while the IUPAC work done on the gas is negative;
* against the final pressure `86100 Pa` the expansion does `43050 J`, strictly less than the
  reversible work;
* Celsius readings are not absolute temperatures inside logarithms.

A heat capacity `Cv T = 20 + T / 100 J/K`, positive and nonconstant on `[300 K, 400 K]`: the
internal energy increases strictly, by `2350 J`, and the endpoint estimate `2300 J` is not exact.
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

-- Fixture: `U T = 20 * T + T ^ 2 / 200` J has `Cv T = 20 + T / 100` J/K, positive and
-- nonconstant on `[300, 400]` K, so `U` is strictly increasing there. Heating from `300` K to
-- `400` K changes the energy by `∫ Cv = 2350` J; the endpoint estimate `Cv 300 * 100 = 2300` J is
-- `50 = b * (T₂ - T₁) ^ 2 / 2` J short.
example :
    StrictMonoOn (fun T : ℝ => 20 * T + T ^ 2 / 200) (Set.Icc 300 400) ∧
      (∫ T in (300 : ℝ)..400, (20 + 1 / 100 * T)) = 2350 ∧
      ((20 : ℝ) + 1 / 100 * 300) * (400 - 300) = 2300 := by
  have hT : (300 : ℝ) ≤ 400 := by norm_num
  have hU : ∀ T ∈ Set.Icc (300 : ℝ) 400,
      HasDerivAt (fun T : ℝ => 20 * T + T ^ 2 / 200) (20 + 1 / 100 * T) T := by
    intro T _
    have e1 : HasDerivAt (fun T : ℝ => 20 * T) 20 T := by
      simpa using (hasDerivAt_id T).const_mul (20 : ℝ)
    have e2 : HasDerivAt (fun T : ℝ => T ^ 2 / 200) (2 * T / 200) T := by
      simpa using (hasDerivAt_pow 2 T).div_const (200 : ℝ)
    have h := e1.add e2
    have hfun : ((fun T : ℝ => 20 * T) + (fun T : ℝ => T ^ 2 / 200))
        = fun T => 20 * T + T ^ 2 / 200 := rfl
    have hder : (20 : ℝ) + 2 * T / 200 = 20 + 1 / 100 * T := by ring
    rw [hfun, hder] at h
    exact h
  have hcont : ContinuousOn (fun T : ℝ => 20 + 1 / 100 * T) (Set.Icc 300 400) :=
    (continuous_const.add (continuous_const.mul continuous_id')).continuousOn
  have hpos : ∀ T ∈ Set.Icc (300 : ℝ) 400, 0 < 20 + 1 / 100 * T := by
    intro T hTmem
    have h300 : (300 : ℝ) ≤ T := hTmem.1
    have hTnn : (0 : ℝ) ≤ T := by linarith
    positivity
  have hmono := strictMonoOn_of_heatCapacity_pos _ _ hT hU hcont hpos
  refine ⟨hmono.1, ?_, ?_⟩
  · have hI := integral_linear_heatCapacity (20 : ℝ) (1 / 100 : ℝ) (300 : ℝ) (400 : ℝ)
    rw [hI]
    norm_num
  · norm_num

end PhyslibExtTest.Thermodynamics.ProcessPorts
