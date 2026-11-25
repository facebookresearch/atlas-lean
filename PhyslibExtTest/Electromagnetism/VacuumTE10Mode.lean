/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.VacuumTE10Mode

@[expose] public section

open PhyslibExt.Electromagnetism.RectangularPECTraces
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
open PhyslibExt.Electromagnetism.VacuumTE10Mode

namespace PhyslibExtTest.Electromagnetism.VacuumTE10Mode

/-- A guide of width `π` has cutoff wavenumber `1`. -/
example : cutoffWavenumber Real.pi = 1 := by
  unfold cutoffWavenumber
  exact div_self Real.pi_ne_zero

/-- At unit speed, `ω = √2` and `β = 1` solve the dispersion relation for width `π`. -/
example : te10Dispersion ((1 : SpeedOfLight) : ℝ) Real.pi (Real.sqrt 2) 1 := by
  unfold te10Dispersion cutoffWavenumber
  rw [div_self Real.pi_ne_zero, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `ω = √2` is above the cutoff `c kc = 1`, so a propagating mode exists. -/
example : ((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi ≤ Real.sqrt 2 := by
  refine (exists_nonneg_te10Dispersion_iff 1 Real.pi (Real.sqrt 2) Real.pi_pos
    (by positivity)).mp ⟨1, zero_le_one, ?_⟩
  unfold te10Dispersion cutoffWavenumber
  rw [div_self Real.pi_ne_zero, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The propagation constant at `ω = √2` is `1`. -/
example : propagationConstant ((1 : SpeedOfLight) : ℝ) Real.pi (Real.sqrt 2) = 1 := by
  unfold propagationConstant cutoffWavenumber
  rw [div_self Real.pi_ne_zero, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The headline result for `a = π`, `b = 1`, `E0 = 1`, `ω = √2`, `β = 1` at unit speed: its
hypotheses are jointly satisfiable, and it returns `β = 1` as the propagation constant. -/
example : (1 : ℝ) = propagationConstant ((1 : SpeedOfLight) : ℝ) Real.pi (Real.sqrt 2) := by
  have hdisp : te10Dispersion ((1 : SpeedOfLight) : ℝ) Real.pi (Real.sqrt 2) 1 := by
    unfold te10Dispersion cutoffWavenumber
    rw [div_self Real.pi_ne_zero, Real.sq_sqrt (by norm_num)]
    norm_num
  exact (te10Mode_correct 1 Real.pi 1 1 (Real.sqrt 2) 1 Real.pi_pos one_pos one_ne_zero
    (by positivity) zero_le_one hdisp).2.2.2.2.2

/-- The same fields satisfy the PEC traces of the `π × 1` guide at time `0`. -/
example : rectangularGuidePECTraces Real.pi 1
    (fieldAtTime (te10ElectricField Real.pi 1 (Real.sqrt 2) 1) 0)
    (fieldAtTime (te10MagneticField Real.pi 1 (Real.sqrt 2) 1) 0) :=
  te10_rectangularGuidePECTraces Real.pi 1 1 (Real.sqrt 2) 1 Real.pi_pos one_pos 0

/-- Validation value: at the guide center, `t = z = 0`, the electric component `E_y` is `E0`. -/
example : te10ElectricField Real.pi 1 (Real.sqrt 2) 1 0 (Real.pi / 2) 0 0 1 = 1 :=
  te10ElectricField_center Real.pi 1 (Real.sqrt 2) 1 Real.pi_ne_zero (by positivity) 0

/-- At the cutoff `ω = c kc = 1` the only solution of the dispersion relation is `β = 0`. -/
example (beta : ℝ) :
    te10Dispersion ((1 : SpeedOfLight) : ℝ) Real.pi
      (((1 : SpeedOfLight) : ℝ) * cutoffWavenumber Real.pi) beta ↔ beta = 0 :=
  te10Dispersion_at_cutoff_iff 1 Real.pi beta Real.pi_pos

/-- Below cutoff, at `ω = 1 / 2 < 1`, no real propagation constant exists. -/
example : ¬ ∃ beta : ℝ, te10Dispersion ((1 : SpeedOfLight) : ℝ) Real.pi (1 / 2) beta := by
  refine not_exists_te10Dispersion_below_cutoff 1 Real.pi (1 / 2) Real.pi_pos
    (by norm_num) ?_
  unfold cutoffWavenumber
  rw [div_self Real.pi_ne_zero]
  norm_num

/-- Below cutoff, at `ω = 1 / 2`, no nonnegative propagation constant exists either. -/
example : ¬ ∃ beta : ℝ, 0 ≤ beta ∧
    te10Dispersion ((1 : SpeedOfLight) : ℝ) Real.pi (1 / 2) beta := by
  rw [exists_nonneg_te10Dispersion_iff 1 Real.pi (1 / 2) Real.pi_pos (by norm_num)]
  unfold cutoffWavenumber
  rw [div_self Real.pi_ne_zero]
  norm_num

/-- Violated premise: `β = 0` at `ω = √2` misses the dispersion relation, and the fields fail
the source-free Maxwell equations. -/
example : ¬ sourceFreeVacuumMaxwell 1 (te10ElectricField Real.pi 1 (Real.sqrt 2) 0)
    (te10MagneticField Real.pi 1 (Real.sqrt 2) 0) := by
  refine not_te10_sourceFreeVacuumMaxwell_of_not_dispersion 1 Real.pi 1 (Real.sqrt 2) 0
    Real.pi_pos one_ne_zero (by positivity) ?_
  unfold te10Dispersion cutoffWavenumber
  rw [div_self Real.pi_ne_zero, Real.sq_sqrt (by norm_num)]
  norm_num

end PhyslibExtTest.Electromagnetism.VacuumTE10Mode
