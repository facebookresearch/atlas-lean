/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.VacuumTE10Evanescent

@[expose] public section

open PhyslibExt.Electromagnetism.RectangularPECTraces
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
open PhyslibExt.Electromagnetism.VacuumTE10Evanescent

namespace PhyslibExtTest.Electromagnetism.VacuumTE10Evanescent

/-- A guide of width `π` has cutoff wavenumber `1`. -/
example : cutoffWavenumber Real.pi = 1 := by
  unfold cutoffWavenumber
  exact div_self Real.pi_ne_zero

/-- At unit speed, `ω = 3 / 5` is strictly below the cutoff `c kc = 1` of a guide of width `π`. -/
example : (3 / 5 : ℝ) < ((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi := by
  unfold cutoffWavenumber
  rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
  norm_num

/-- At unit speed and width `π`, the decay rate at `ω = 3 / 5` is `4 / 5`. -/
example : decayRate ((1 : SpeedOfLight) : ℝ) Real.pi (3 / 5) = 4 / 5 := by
  unfold decayRate cutoffWavenumber
  rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one,
    show (1 : ℝ) ^ 2 - (3 / 5) ^ 2 / 1 ^ 2 = (4 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The fixture rate `4 / 5` is positive and squares to `kc^2 - ω^2 / c^2 = 16 / 25`. -/
example : 0 < decayRate ((1 : SpeedOfLight) : ℝ) Real.pi (3 / 5) ∧
    decayRate ((1 : SpeedOfLight) : ℝ) Real.pi (3 / 5) ^ 2 = 16 / 25 := by
  have hbelow : (3 / 5 : ℝ) < ((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi := by
    unfold cutoffWavenumber
    rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
    norm_num
  refine ⟨decayRate_pos 1 Real.pi (3 / 5) (by norm_num) hbelow, ?_⟩
  rw [decayRate_sq 1 Real.pi (3 / 5) (by norm_num) hbelow]
  unfold cutoffWavenumber
  rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
  norm_num

/-- At the cutoff `ω = c kc` the decay rate is `0`. -/
example : decayRate ((1 : SpeedOfLight) : ℝ) Real.pi
    (((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi) = 0 :=
  decayRate_at_cutoff 1 Real.pi

/-- With the fixture rate `κ = 4 / 5`, the evanescent fields of a guide of width `π` at
`ω = 3 / 5` satisfy the source-free vacuum Maxwell equations at unit speed. -/
example : sourceFreeVacuumMaxwell 1 (evanescentElectricField Real.pi 1 (3 / 5) (4 / 5))
    (evanescentMagneticField Real.pi 1 (3 / 5) (4 / 5)) := by
  have hbelow : (3 / 5 : ℝ) < ((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi := by
    unfold cutoffWavenumber
    rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
    norm_num
  have hrate : decayRate ((1 : SpeedOfLight) : ℝ) Real.pi (3 / 5) = 4 / 5 := by
    unfold decayRate cutoffWavenumber
    rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one,
      show (1 : ℝ) ^ 2 - (3 / 5) ^ 2 / 1 ^ 2 = (4 / 5) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h := evanescent_sourceFreeVacuumMaxwell 1 Real.pi 1 (3 / 5) (by norm_num) hbelow
  rwa [hrate] at h

/-- The rate `κ = 0` below cutoff (`ω = 3 / 5`, `kc = 1`) violates `ω^2 = c^2 (kc^2 - κ^2)`, so
the undamped field breaks the source-free vacuum Maxwell equations. -/
example : ¬ sourceFreeVacuumMaxwell 1 (evanescentElectricField Real.pi 1 (3 / 5) 0)
    (evanescentMagneticField Real.pi 1 (3 / 5) 0) := by
  refine not_evanescent_sourceFreeVacuumMaxwell_of_wrong_rate 1 Real.pi 1 (3 / 5) 0
    Real.pi_pos one_ne_zero (by norm_num) ?_
  unfold cutoffWavenumber
  rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
  norm_num

/-- At every time the fixture fields satisfy the PEC traces of the guide of widths `π` and `1`. -/
example (t : ℝ) : rectangularGuidePECTraces Real.pi 1
    (fieldAtTime (evanescentElectricField Real.pi 1 (3 / 5) (4 / 5)) t)
    (fieldAtTime (evanescentMagneticField Real.pi 1 (3 / 5) (4 / 5)) t) :=
  evanescent_rectangularGuidePECTraces Real.pi 1 1 (3 / 5) (4 / 5) Real.pi_pos one_pos t

/-- At `x = π / 2`, `t = z = 0` the fixture electric component `E_y` equals the amplitude `1`. -/
example (y : ℝ) : evanescentElectricField Real.pi 1 (3 / 5) (4 / 5) 0 (Real.pi / 2) y 0 1 = 1 :=
  evanescentElectricField_center Real.pi 1 (3 / 5) (4 / 5) Real.pi_ne_zero (by norm_num) y

/-- The fixture electric field is not identically zero. -/
example : evanescentElectricField Real.pi 1 (3 / 5) (4 / 5) ≠ 0 :=
  evanescentElectricField_ne_zero Real.pi 1 (3 / 5) (4 / 5) Real.pi_pos one_ne_zero
    (by norm_num)

/-- The fixture electric component `E_y` is explicit. -/
example (t x y z : ℝ) : evanescentElectricField Real.pi 1 (3 / 5) (4 / 5) t x y z 1 =
    Real.sin (cutoffWavenumber Real.pi * x) * Real.exp (-(4 / 5) * z) *
      Real.cos (3 / 5 * t) := by
  rw [evanescentElectricField_apply Real.pi 1 (3 / 5) (4 / 5) (by norm_num)]
  simp

/-- At `z = 5` every fixture electric component is bounded by `exp (-4)`. -/
example (t x y : ℝ) (i : Fin 3) :
    |evanescentElectricField Real.pi 1 (3 / 5) (4 / 5) t x y 5 i| ≤ Real.exp (-4) := by
  have h := (evanescentFields_abs_le Real.pi 1 (3 / 5) (4 / 5) Real.pi_pos (by norm_num)
    (by norm_num) t x y 5 (by norm_num) i).1
  rw [abs_one, one_mul, show -(4 / 5 : ℝ) * 5 = -4 by norm_num] at h
  exact h

/-- Every fixture magnetic component tends to zero as `z → ∞`. -/
example (t x y : ℝ) (i : Fin 3) : Filter.Tendsto
    (fun z => evanescentMagneticField Real.pi 1 (3 / 5) (4 / 5) t x y z i) Filter.atTop
    (nhds 0) :=
  (tendsto_evanescentFields_atTop Real.pi 1 (3 / 5) (4 / 5) (by norm_num) t x y i).2

/-- The fixture field grows toward negative `z`: `E_y` at `t = 0`, `x = π / 2` is unbounded on
`z ≤ 0`. -/
example (y : ℝ) : ¬ ∃ C : ℝ, ∀ z : ℝ, z ≤ 0 →
    |evanescentElectricField Real.pi 1 (3 / 5) (4 / 5) 0 (Real.pi / 2) y z 1| ≤ C :=
  not_bddAbove_evanescentElectricField_nonpos Real.pi 1 (3 / 5) (4 / 5) Real.pi_pos one_ne_zero
    (by norm_num) (by norm_num) y

/-- The combined statement holds for the fixture. -/
example : 0 < decayRate ((1 : SpeedOfLight) : ℝ) Real.pi (3 / 5) ∧
    sourceFreeVacuumMaxwell 1
      (evanescentElectricField Real.pi 1 (3 / 5) (decayRate ((1 : SpeedOfLight) : ℝ) Real.pi
        (3 / 5)))
      (evanescentMagneticField Real.pi 1 (3 / 5) (decayRate ((1 : SpeedOfLight) : ℝ) Real.pi
        (3 / 5))) := by
  have hbelow : (3 / 5 : ℝ) < ((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi := by
    unfold cutoffWavenumber
    rw [div_self Real.pi_ne_zero, SpeedOfLight.val_one]
    norm_num
  obtain ⟨hpos, -, hbulk, -⟩ :=
    te10Evanescent_correct 1 Real.pi 1 1 (3 / 5) Real.pi_pos one_pos one_ne_zero (by norm_num)
      hbelow
  exact ⟨hpos, hbulk⟩

end PhyslibExtTest.Electromagnetism.VacuumTE10Evanescent
