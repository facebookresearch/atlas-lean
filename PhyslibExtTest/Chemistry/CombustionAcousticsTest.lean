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

/-- Finite-horizon regression: the equilibrium trajectory on
`[0, 1]` with a discontinuous extension after `1` still satisfies
the interval trapping conclusion at `t = 1`, because the interval
API only sees the derivative domain `Set.Icc 0 1`. -/
example : ∃ Te : ℝ, Te ∈ Set.Ioo 1 (1 + 1 / 1) ∧
    (fun s : ℝ => if s ≤ 1 then Te else 0) 1 ∈
      Set.Icc (min ((fun s : ℝ => if s ≤ 1 then Te else 0) 0) 1)
        (max ((fun s : ℝ => if s ≤ 1 then Te else 0) 0) (1 + 1 / 1)) := by
  obtain ⟨Te, hTe, hrate⟩ :=
    Chemistry.CombustionAcoustics.arrhenius_equilibrium_exists (G := 1) (H := 1)
      (B := 1) (Ta := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨Te, hTe, ?_⟩
  have hderiv : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s : ℝ => if s ≤ 1 then Te else 0)
        (Chemistry.CombustionAcoustics.arrheniusRate 1 1 1 1
          ((fun s : ℝ => if s ≤ 1 then Te else 0) s) / 1)
        (Set.Icc 0 1) s := by
    intro s hs
    have hfun : (fun s : ℝ => if s ≤ 1 then Te else 0) s = Te := if_pos hs.2
    rw [hfun, hrate]
    have hconst := hasDerivWithinAt_const s (Set.Icc (0 : ℝ) 1) Te
    refine hconst.congr_of_eventuallyEq ?_ ?_
    · exact Filter.EventuallyEq.of_mem self_mem_nhdsWithin
        (fun y hy => if_pos hy.2)
    · exact if_pos hs.2
  have h := Chemistry.CombustionAcoustics.arrhenius_solution_trapped_on_interval
    (G := 1) (H := 1) (B := 1) (Ta := 1) (C := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (t := 1) (by norm_num) hderiv
  simpa using h
