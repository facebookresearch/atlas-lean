/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.CombustionAcoustics

/-!
# Arrhenius equilibrium checks

Concrete consumers of `PhyslibExt.Chemistry.CombustionAcoustics`:
unit-rate parameters `G = H = B = Ta = 1`, whose equilibrium lies in
`(1, 2)` with zero rate, and the constant solution at an equilibrium
is trapped.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter equilibrium

## iv. References

- `PhyslibExt.Chemistry.CombustionAcoustics`
-/

/-- An equilibrium in `(1, 2)` for the unit parameters. -/
example : ∃ T : ℝ, T ∈ Set.Ioo 1 (1 + 1 / 1) ∧
    Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1 T = 0 :=
  Chemistry.CombustionAcoustics.arrhenius_equilibrium_exists (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The rate at ambient `1` is `exp (-1)`, positive. -/
example : Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1 1 = Real.exp (-1) ∧
    0 < Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1 1 :=
  ⟨by simpa using Chemistry.CombustionAcoustics.arrheniusRate_ambient 1 1 1 1,
   Chemistry.CombustionAcoustics.arrheniusRate_pos_ambient (by norm_num)⟩

/-- Trapping API on the constant equilibrium solution: for the
equilibrium `Te` of the unit parameters, the constant trajectory
`T = Te` has zero within-derivative, the rate vanishes there, and
the trapping theorem keeps it in `[min Te 1, max Te 2]`. -/
example : ∃ Te : ℝ, Te ∈ Set.Ioo 1 (1 + 1 / 1) ∧
    Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1 Te = 0 ∧
      ∀ t : ℝ, 0 ≤ t → (fun _ : ℝ => Te) t ∈
        Set.Icc (min ((fun _ : ℝ => Te) 0) 1)
          (max ((fun _ : ℝ => Te) 0) (1 + 1 / 1)) := by
  obtain ⟨Te, hTe, hrate⟩ :=
    Chemistry.CombustionAcoustics.arrhenius_equilibrium_exists (G := 1) (H := 1)
      (B := 1) (Ta := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨Te, hTe, hrate, fun t ht => ?_⟩
  have hderiv : ∀ s : ℝ, 0 ≤ s →
      HasDerivWithinAt (fun _ : ℝ => Te)
        (Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1 Te / 1) (Set.Ici 0) s := by
    intro s _
    rw [hrate]
    simpa using hasDerivWithinAt_const s (Set.Ici 0) Te
  have h := Chemistry.CombustionAcoustics.arrhenius_solution_trapped (G := 1)
    (H := 1) (B := 1) (Ta := 1) (C := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hderiv ht
  simpa using h

/-- Acoustic energy consumers: gamma 2, pbar and rho 1, L pi, constant mode A 0 and B 1, r 0, H 2. -/
example :
    HasDerivAt (fun s : ℝ => Chemistry.CombustionAcoustics.acousticModeEnergy
        2 1 1 Real.pi ((fun _ : ℝ => 0) s) ((fun _ : ℝ => 1) s))
      0 (0 : ℝ) := by
  have h := Chemistry.CombustionAcoustics.hasDerivAt_acousticModeEnergy
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 0)
    (H := 2) (by norm_num) (by norm_num) (by norm_num) Real.pi_ne_zero
    (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 1) (A' := 0) (B' := 0) (t := 0)
    (hasDerivAt_const 0 0) (hasDerivAt_const 0 1)
    (by field_simp; ring) (by field_simp; ring)
  simpa using h

/-- Integral form for the same constant mode. -/
example :
    Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        ((fun _ : ℝ => 0) 1) ((fun _ : ℝ => 1) 1) -
      Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        ((fun _ : ℝ => 0) 0) ((fun _ : ℝ => 1) 0) = 0 := by
  have h := Chemistry.CombustionAcoustics.acousticModeEnergy_sub_eq_integral
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 0)
    (H := 2) (by norm_num) (by norm_num) (by norm_num) Real.pi_pos
    (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 1) (A' := fun _ : ℝ => 0)
    (B' := fun _ : ℝ => 0)
    (fun t => hasDerivAt_const t 0) (fun t => hasDerivAt_const t 1)
    (fun t => by field_simp; ring) (fun t => by field_simp; ring) 0 1
  simpa using h
