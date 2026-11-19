/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Thermodynamics.GasCycles

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Thermodynamics.GasCycles`

A freezer between `250 K` and `300 K` that absorbs `4000 J` per cycle for `1000 J` of work:

* its Clausius residual is `2/3 J/K` and both coefficients of performance lie strictly below the
  reversible bounds `5` and `6`;
* the general results apply to it: the Clausius inequality forces positive work, the bounds hold,
  and the reversible machine (`5000 J` absorbed, `6000 J` rejected) attains them.

At equal reservoir temperatures `300 K` the coefficients have no finite bound: some admissible
cycle has both coefficients above `10`.

An ideal Otto loop of a monatomic gas (`Cv = 3 J/K`, `nR = 2 J/K`, `γ = 5/3`) compressed by `8`
from `300 K` and heated by `3000 J`:

* its states are `1200 K`, `2200 K` and `550 K`; it rejects `750 J` and does `2250 J` of net work;
* the general results apply to it: both legs lie on the adiabat, the rejected heat and the net
  work are positive, and the work-to-heat ratio is `ottoEfficiency 8 (5/3) = 3/4`;
* with zero heat input it does no work, and `0 / 0` is not the efficiency.
-/

@[expose] public section

namespace PhyslibExtTest.Thermodynamics.GasCycles

open _root_.GasCycles

-- Fixture: a freezer between `Tc = 250` K and `Th = 300` K absorbs `Qc = 4000` J and takes
-- `W = 1000` J, rejecting `Qh = 5000` J. Its Clausius residual is `2/3` J/K, and
-- `COP_R = 4 < 5 = Tc / (Th - Tc)`, `COP_HP = 5 < 6 = Th / (Th - Tc)`. The reversible machine with
-- `Qc = 5000` J and `Qh = 6000` J has zero residual and attains both bounds.
example :
    (5000 : ℝ) / 300 - 4000 / 250 = 2 / 3 ∧ (4000 : ℝ) / 1000 < 250 / (300 - 250) ∧
      (5000 : ℝ) / 1000 < 300 / (300 - 250) ∧ (6000 : ℝ) / 300 - 5000 / 250 = 0 ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) ∧ (6000 : ℝ) / 1000 = 300 / (300 - 250) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

-- The freezer and the reversible machine through the general results: the Clausius inequality
-- forces positive work, both coefficients of performance obey the reversible bounds, and the
-- reversible machine attains the refrigerator bound because its Clausius residual is zero.
example :
    (0 : ℝ) < 1000 ∧
      ((4000 : ℝ) / 1000 ≤ 250 / (300 - 250) ∧ (5000 : ℝ) / 1000 ≤ 300 / (300 - 250)) ∧
      (5000 : ℝ) / 1000 = 250 / (300 - 250) := by
  refine ⟨work_pos_of_clausius (Qh := 5000) (Qc := 4000) (Tc := 250) (Th := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    cop_le_carnot (Qh := 5000) (Qc := 4000) (W := 1000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), ?_⟩
  exact (cop_eq_carnot_iff (Qh := 6000) (Qc := 5000) (W := 1000) (Tc := 250) (Th := 300)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1.2 (by norm_num)

-- Equal reservoir temperatures, `T = 300` K, and the bound `M = 10`: `cop_unbounded_of_eq` gives
-- an admissible cycle (`Qc > 0`, `W = Qh - Qc > 0`, Clausius inequality) whose coefficients of
-- performance both exceed `10`, so `10` is not an upper bound on `COP_R` over all admissible
-- cycles at that temperature.
example :
    (∃ Qh Qc W : ℝ, 0 < Qc ∧ W = Qh - Qc ∧ 0 < W ∧ 0 ≤ Qh / 300 - Qc / 300 ∧
        10 < Qc / W ∧ 10 < Qh / W) ∧
      ¬ ∀ Qh Qc W : ℝ, 0 < Qc → W = Qh - Qc → 0 < W → 0 ≤ Qh / 300 - Qc / 300 →
        Qc / W ≤ 10 := by
  have h := cop_unbounded_of_eq (T := 300) (by norm_num) 10
  refine ⟨h, fun hall => ?_⟩
  obtain ⟨Qh, Qc, W, hQc, hW, hWpos, hcl, hR, -⟩ := h
  have hle := hall Qh Qc W hQc hW hWpos hcl
  linarith

-- Fixture: a monatomic ideal gas (`Cv = 3` J/K, `nR = 2` J/K, so `γ = 5/3`) compressed by
-- `r = 8` from `T₁ = 300` K and heated by `Qin = 3000` J reaches `T₂ = 1200` K, `T₃ = 2200` K and
-- `T₄ = 550` K, rejects `750` J and does `2250` J of net work: `η = 3/4 = 1 - 8 ^ (1 - 5/3)`.
example :
    ottoCompressedTemp 300 8 (5 / 3) = 1200 ∧ ottoPeakTemp 300 8 (5 / 3) 3 3000 = 2200 ∧
      ottoExpandedTemp 300 8 (5 / 3) 3 3000 = 550 ∧ ottoHeatOut 300 8 (5 / 3) 3 3000 = 750 ∧
      ottoNetWork 300 8 (5 / 3) 3 3000 = 2250 ∧ ottoEfficiency 8 (5 / 3) = 3 / 4 := by
  have h8_23 : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
    have h8 : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : ((3 : ℕ) : ℝ) * ((2 : ℝ) / 3) = 2 := by norm_num
    rw [hexp, Real.rpow_two]
    norm_num
  have h23 : (5 / 3 - 1 : ℝ) = (2 : ℝ) / 3 := by norm_num
  have h8_comp : (8 : ℝ) ^ (5 / 3 - 1 : ℝ) = 4 := by
    rw [h23, h8_23]
  have hneg : (1 - 5 / 3 : ℝ) = -((2 : ℝ) / 3) := by norm_num
  have h8_neg : (8 : ℝ) ^ (1 - 5 / 3 : ℝ) = 1 / 4 := by
    rw [hneg, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), h8_23]
    norm_num
  have hcomp : ottoCompressedTemp 300 8 (5 / 3) = 1200 := by
    simp only [ottoCompressedTemp]
    rw [h8_comp]
    norm_num
  have hpeak : ottoPeakTemp 300 8 (5 / 3) 3 3000 = 2200 := by
    simp only [ottoPeakTemp, hcomp]
    norm_num
  have hexp : ottoExpandedTemp 300 8 (5 / 3) 3 3000 = 550 := by
    simp only [ottoExpandedTemp, hpeak]
    rw [h8_neg]
    norm_num
  have hheat : ottoHeatOut 300 8 (5 / 3) 3 3000 = 750 := by
    simp only [ottoHeatOut, hexp]
    norm_num
  have hwork : ottoNetWork 300 8 (5 / 3) 3 3000 = 2250 := by
    simp only [ottoNetWork, hpeak, hexp, hcomp]
    norm_num
  have heff : ottoEfficiency 8 (5 / 3) = 3 / 4 := by
    simp only [ottoEfficiency]
    rw [h8_neg]
    norm_num
  exact ⟨hcomp, hpeak, hexp, hheat, hwork, heff⟩

-- The monatomic loop through the general results: `otto_cycle` puts the compression leg on the
-- adiabat and gives positive rejected heat and net work, and `ottoNetWork_div_heatIn` identifies
-- the work-to-heat ratio with `ottoEfficiency 8 (5/3)`, which is `3/4` because `8 ^ (2/3) = 4`.
example :
    ottoCompressedTemp 300 8 (5 / 3) * (1 / 8) ^ ((5 : ℝ) / 3 - 1) = 300 * 1 ^ ((5 : ℝ) / 3 - 1) ∧
      0 < ottoHeatOut 300 8 (5 / 3) 3 3000 ∧ 0 < ottoNetWork 300 8 (5 / 3) 3 3000 ∧
      ottoNetWork 300 8 (5 / 3) 3 3000 / 3000 = ottoEfficiency 8 (5 / 3) ∧
      ottoEfficiency 8 (5 / 3) = 3 / 4 := by
  obtain ⟨hc, -, -, hq, hw, -⟩ := otto_cycle (T₁ := 300) (V₁ := 1) (r := 8) (γ := 5 / 3)
    (Cv := 3) (nR := 2) (Qin := 3000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have h8 : (8 : ℝ) ^ (1 - (5 : ℝ) / 3) = 1 / 4 := by
    rw [show (1 : ℝ) - 5 / 3 = -(2 / 3) by norm_num, Real.rpow_neg (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨hc, hq, hw,
    (ottoNetWork_div_heatIn (T₁ := 300) (by norm_num) (by norm_num) (by norm_num)).1, ?_⟩
  rw [ottoEfficiency, h8]
  norm_num

-- Zero heat input on the same gas: the loop does no net work, and the work-to-heat ratio `0 / 0`
-- is not the Otto efficiency.
example :
    ottoNetWork 300 8 (5 / 3) 3 0 = 0 ∧
      ottoNetWork 300 8 (5 / 3) 3 0 / 0 ≠ ottoEfficiency 8 (5 / 3) :=
  otto_zero_heatIn (by norm_num) (by norm_num)

end PhyslibExtTest.Thermodynamics.GasCycles
