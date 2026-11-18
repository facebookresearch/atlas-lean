/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.SeparableVacuumMaxwell
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open scoped ContDiff
open PhyslibExt.Electromagnetism.SeparableGuidePotential
open PhyslibExt.Electromagnetism.SeparableVacuumMaxwell

namespace PhyslibExtTest.Electromagnetism.SeparableVacuumMaxwell

/-- The sine profile at cutoff `1` satisfies the profile equation. -/
example : profileEquation (fun x => Real.sin (1 * x)) 1 :=
  ((propagatingMode_satisfies_scalarEquations 1 0 1 1).mpr (by norm_num)).1

/-- The mode `cos t` at speed `1` satisfies the mode equation. -/
example : modeEquation 1 1 (fun t z => Real.cos (1 * t - 0 * z)) :=
  ((propagatingMode_satisfies_scalarEquations 1 0 1 1).mpr (by norm_num)).2

/-- The same concrete fields satisfy the source-free Maxwell equations. -/
example : sourceFreeVacuumMaxwell 1
    (separableElectricField (fun x => Real.sin (1 * x)) (fun t z => Real.cos (1 * t - 0 * z)))
    (separableMagneticField (fun x => Real.sin (1 * x)) (fun t z => Real.cos (1 * t - 0 * z))) :=
  propagatingMode_sourceFreeVacuumMaxwell 1 0 1 1 (by norm_num)

/-- The canonical Physlib fields of the same guide potential satisfy the source-free equations. -/
example : sourceFreeVacuumMaxwellFields 1
    ((separableGuidePotential 1 (fun x => Real.sin (1 * x))
      (fun t z => Real.cos (1 * t - 0 * z))).electricField 1)
    ((separableGuidePotential 1 (fun x => Real.sin (1 * x))
      (fun t z => Real.cos (1 * t - 0 * z))).magneticField 1) := by
  obtain ⟨hprof, hmode⟩ := (propagatingMode_satisfies_scalarEquations 1 0 1 1).mpr (by norm_num)
  have hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.cos (1 * p.1 - 0 * p.2)) := by fun_prop
  exact separableGuidePotential_sourceFreeVacuumMaxwellFields 1 _ _ 1 (by fun_prop) hf hprof hmode

/-- Magnetic Gauss's law needs no regularity: a non-differentiable mode still works. -/
example : ∀ t x y z, spaceDivergence (separableMagneticField (fun x => x ^ 3) (fun _ z => |z|))
    t x y z = 0 :=
  separable_divergence_magnetic _ _

/-- Quarter-period electric component: at `t = x = π / 2` the field is `(0, 1, 0)`. -/
example : separableElectricField (fun x => Real.sin (1 * x)) (fun t z => Real.cos t)
    (Real.pi / 2) (Real.pi / 2) 0 0 = ![0, 1, 0] := by
  have hpt : partialTime (fun t z => Real.cos t) (Real.pi / 2) 0 = -1 := by
    unfold partialTime
    rw [Real.deriv_cos, Real.sin_pi_div_two]
  simp [separableElectricField, hpt, Real.sin_pi_div_two]

/-- Quarter-period magnetic component: at `t = x = π / 2` the field vanishes. -/
example : separableMagneticField (fun x => Real.sin (1 * x)) (fun t z => Real.cos t)
    (Real.pi / 2) (Real.pi / 2) 0 0 = ![0, 0, 0] := by
  have hpz : partialZ (fun t z => Real.cos t) (Real.pi / 2) 0 = 0 := by
    unfold partialZ
    simp
  have hda : deriv (fun x => Real.sin (1 * x)) (Real.pi / 2) = 0 := by
    have hfun : (fun x : ℝ => Real.sin (1 * x)) = Real.sin := by
      funext x
      simp
    rw [hfun, Real.deriv_sin, Real.cos_pi_div_two]
  simp [separableMagneticField, hpz, hda, Real.sin_pi_div_two, Real.cos_pi_div_two]

end PhyslibExtTest.Electromagnetism.SeparableVacuumMaxwell
