/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.CombustionAcoustics
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum

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
- B. Semenov critical-ratio folds
- C. Frank-Kamenetskii criticality and box exit

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
    (by norm_num) (by norm_num) (by norm_num) hderiv
    (fun s _ => lt_trans zero_lt_one hTe.1) ht
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
    have hev : (fun s : ℝ => if s ≤ 1 then Te else 0) =ᶠ[nhdsWithin s (Set.Icc (0 : ℝ) 1)]
        (fun _ : ℝ => Te) :=
      Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun y hy => if_pos hy.2)
    have h := hconst.congr_of_eventuallyEq hev (if_pos hs.2)
    simpa using h
  have h := Chemistry.CombustionAcoustics.arrhenius_solution_trapped_on_interval
    (G := 1) (H := 1) (B := 1) (Ta := 1) (C := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (t := 1) (by norm_num) hderiv
    (fun s hs => by
      show 0 < (if s ≤ 1 then Te else (0 : ℝ))
      rw [if_pos hs.2]
      exact lt_trans zero_lt_one hTe.1)
  simpa using h

/-- Acoustic energy consumers: gamma 2, pbar and rho 1, L pi, constant mode A 0 and B 1, r 0, H 2. -/
example :
    HasDerivAt (fun s : ℝ => Chemistry.CombustionAcoustics.acousticModeEnergy
        2 1 1 Real.pi ((fun _ : ℝ => 0) s) ((fun _ : ℝ => 1) s))
      0 (0 : ℝ) := by
  have h := Chemistry.CombustionAcoustics.hasDerivAt_acousticModeEnergy
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 0)
    (H := 2) (by norm_num) (by norm_num) Real.pi_ne_zero
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
    (H := 2) (by norm_num) (by norm_num) Real.pi_pos
    (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 1) (A' := fun _ : ℝ => 0)
    (B' := fun _ : ℝ => 0) 0 1
    (fun t _ => hasDerivAt_const t 0) (fun t _ => hasDerivAt_const t 1)
    (fun t _ => by field_simp; ring) (fun t _ => by field_simp; ring)
  simpa using h

/-- Balanced nonzero source and damping: constant mode
`A = B = 1` at `γ = 2`, `pbar = ρ = 1`, `L = π`, `r = 1`,
`H = 2`. The heat-release source `π / 2` and the damping
`π / 2` cancel, so the energy derivative is `0`, with both
terms nonzero. -/
example :
    HasDerivAt (fun s : ℝ => Chemistry.CombustionAcoustics.acousticModeEnergy
        2 1 1 Real.pi ((fun _ : ℝ => 1) s) ((fun _ : ℝ => 1) s))
      (0 : ℝ) (0 : ℝ) := by
  have h := Chemistry.CombustionAcoustics.hasDerivAt_acousticModeEnergy
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 1)
    (H := 2) (by norm_num) (by norm_num) Real.pi_ne_zero
    (A := fun _ : ℝ => 1) (B := fun _ : ℝ => 1) (A' := 0) (B' := 0) (t := 0)
    (hasDerivAt_const 0 1) (hasDerivAt_const 0 1)
    (by field_simp; ring) (by field_simp; ring)
  convert h using 1
  ring

/-- Signed dissipation corollary on a nonconstant trajectory:
`A(s) = 2 - 2s`, `B(s) = 1 + s` at `t = 0`, with `r = 1` and
no heat release, gives derivative `-(π / 2) ≤ 0`. -/
example :
    HasDerivAt (fun s : ℝ => Chemistry.CombustionAcoustics.acousticModeEnergy
        2 1 1 Real.pi (2 - 2 * s) (1 + s))
        (-(Real.pi / 2)) (0 : ℝ) ∧ -(Real.pi / 2) ≤ 0 := by
  have hA : HasDerivAt (fun s : ℝ => 2 - 2 * s) (-2) (0 : ℝ) := by
    have h1 := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have h2 := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).sub h1
    convert h2 using 1
    · first
      | (ext s; simp)
      | norm_num
    · first
      | (ext s; simp)
      | norm_num
  have hB : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) (0 : ℝ) := by
    have h1 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
    convert h1 using 1
    · first
      | (ext s; simp)
      | norm_num
    · first
      | (ext s; simp)
      | norm_num
  have h := Chemistry.CombustionAcoustics.acousticModeEnergy_deriv_nonpos_of_no_heat
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 1)
    (by norm_num) (by norm_num) Real.pi_pos (by norm_num)
    (A := fun s : ℝ => 2 - 2 * s) (B := fun s : ℝ => 1 + s)
    (A' := -2) (B' := 1) (t := 0) hA hB
    (by
      show (-2 : ℝ) = -2 * 1 * (Real.pi / Real.pi) * (1 + 0) + (2 - 1) * 0
      rw [div_self Real.pi_ne_zero]
      norm_num)
    (by
      show (1 : ℝ) * 1 = (Real.pi / Real.pi) * (2 - 2 * 0) - 1 * (1 + 0)
      rw [div_self Real.pi_ne_zero]
      norm_num)
  simpa using h

/-- Conserved-energy corollary on a nonconstant trajectory:
`A(s) = 1 - 2s`, `B(s) = 1 + s` at `t = 0` satisfy the modal
equations with no heat release and no damping. -/
example :
    HasDerivAt (fun s : ℝ => Chemistry.CombustionAcoustics.acousticModeEnergy
        2 1 1 Real.pi (1 - 2 * s) (1 + s)) 0 (0 : ℝ) := by
  have hA : HasDerivAt (fun s : ℝ => 1 - 2 * s) (-2) (0 : ℝ) := by
    have h1 := (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have h2 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h1
    convert h2 using 1
    · first
      | (ext s; simp)
      | norm_num
    · first
      | (ext s; simp)
      | norm_num
  have hB : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) (0 : ℝ) := by
    have h1 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
    convert h1 using 1
    · first
      | (ext s; simp)
      | norm_num
    · first
      | (ext s; simp)
      | norm_num
  have h := Chemistry.CombustionAcoustics.hasDerivAt_acousticModeEnergy_conserved
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi)
    (by norm_num) (by norm_num) Real.pi_ne_zero
    (A := fun s : ℝ => 1 - 2 * s) (B := fun s : ℝ => 1 + s)
    (A' := -2) (B' := 1) (t := 0) hA hB
    (by
      show (-2 : ℝ) = -2 * 1 * (Real.pi / Real.pi) * (1 + 0)
      rw [div_self Real.pi_ne_zero]
      norm_num)
    (by
      show (1 : ℝ) * 1 = (Real.pi / Real.pi) * (1 - 2 * 0)
      rw [div_self Real.pi_ne_zero]
      norm_num)
  simpa using h

/-- Interval balance for the balanced nonzero constant mode
`A = B = r = 1`, `H = 2` over `[0, 1]`: both sides are `0`,
with the source and damping terms nonzero inside the
integrand before cancellation. -/
example :
    Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        ((fun _ : ℝ => 1) 1) ((fun _ : ℝ => 1) 1) -
      Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        ((fun _ : ℝ => 1) 0) ((fun _ : ℝ => 1) 0) =
      ∫ t in (0 : ℝ)..(1 : ℝ),
        (Real.pi * (2 - 1) * (1 : ℝ) * 2 / (2 * 2 * 1) -
          1 * Real.pi * (1 : ℝ) ^ 2 / 2) := by
  have h := Chemistry.CombustionAcoustics.acousticModeEnergy_sub_eq_integral
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 1)
    (H := 2) (by norm_num) (by norm_num) Real.pi_pos
    (A := fun _ : ℝ => 1) (B := fun _ : ℝ => 1) (A' := fun _ : ℝ => 0)
    (B' := fun _ : ℝ => 0) 0 1
    (fun t _ => hasDerivAt_const t 1) (fun t _ => hasDerivAt_const t 1)
    (fun t _ => by field_simp; ring) (fun t _ => by field_simp; ring)
  simpa using h

/-- Genuine conservation on a nonconstant trajectory: with
`A(s) = cos(√2 s)` and `B(s) = (√2/2) sin(√2 s)`, the modal
equations `A' = -2B`, `B' = A` hold at every time for
`γ = 2`, `pbar = ρ = 1`, `L = π`, so the energy at `s = 1`
equals the energy at `s = 0`. -/
example :
    Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        (Real.cos (Real.sqrt 2 * 1))
        ((Real.sqrt 2 / 2) * Real.sin (Real.sqrt 2 * 1)) =
      Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        (Real.cos (Real.sqrt 2 * 0))
        ((Real.sqrt 2 / 2) * Real.sin (Real.sqrt 2 * 0)) := by
  have hA : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.cos (Real.sqrt 2 * s))
      (-Real.sqrt 2 * Real.sin (Real.sqrt 2 * t)) t := fun t => by
    have h := ((hasDerivAt_id t).const_mul (Real.sqrt 2)).cos
    simpa [mul_comm] using h
  have hB : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (Real.sqrt 2 / 2) * Real.sin (Real.sqrt 2 * s))
      (Real.cos (Real.sqrt 2 * t)) t := fun t => by
    have h := (((hasDerivAt_id t).const_mul (Real.sqrt 2)).sin).const_mul
      (Real.sqrt 2 / 2)
    convert h using 1
    · first
      | (funext s; simp)
      | (simp only [id_eq]
         rw [show Real.sqrt 2 / 2 * (Real.cos (Real.sqrt 2 * t) *
              (Real.sqrt 2 * 1))
            = Real.cos (Real.sqrt 2 * t) * ((Real.sqrt 2 * Real.sqrt 2) / 2)
            by ring,
          Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
         norm_num)
    · first
      | (funext s; simp)
      | (simp only [id_eq]
         rw [show Real.sqrt 2 / 2 * (Real.cos (Real.sqrt 2 * t) *
              (Real.sqrt 2 * 1))
            = Real.cos (Real.sqrt 2 * t) * ((Real.sqrt 2 * Real.sqrt 2) / 2)
            by ring,
          Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
         norm_num)
  exact Chemistry.CombustionAcoustics.acousticModeEnergy_eq_of_conserved
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi)
    (by norm_num) (by norm_num) Real.pi_pos hA hB
    (fun t => by
      show -Real.sqrt 2 * Real.sin (Real.sqrt 2 * t) =
        -2 * 1 * (Real.pi / Real.pi) * ((Real.sqrt 2 / 2) *
          Real.sin (Real.sqrt 2 * t))
      rw [div_self Real.pi_ne_zero]
      ring)
    (fun t => by
      show (1 : ℝ) * Real.cos (Real.sqrt 2 * t) =
        (Real.pi / Real.pi) * Real.cos (Real.sqrt 2 * t)
      rw [div_self Real.pi_ne_zero])
    0 1

/-- Nonzero accumulated interval balance: the decaying solution
`A(t) = 2 * exp (-t)`, `B(t) = exp (-t)` of the modal equations
with `γ = 2`, `pbar = ρ = 1`, `L = π`, `r = 3`, `H = 0` has
endpoint energies differing by the nonzero integral
`-3π (1 - exp (-2)) / 4` over `[0, 1]`. -/
example :
    Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        (2 * Real.exp (-(1 : ℝ))) (Real.exp (-(1 : ℝ))) -
      Chemistry.CombustionAcoustics.acousticModeEnergy 2 1 1 Real.pi
        (2 * Real.exp (-(0 : ℝ))) (Real.exp (-(0 : ℝ))) =
      -3 * Real.pi * (1 - Real.exp (-2)) / 4 := by
  have hA : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 2 * Real.exp (-s))
        (-2 * Real.exp (-t)) t := by
    intro t _
    have h := ((hasDerivAt_id t).neg.exp).const_mul (2 : ℝ)
    convert h using 1
    · first
      | (funext s; simp)
      | simp
    · first
      | (funext s; simp)
      | simp
  have hB : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    intro t _
    have h := (hasDerivAt_id t).neg.exp
    simpa using h
  have h := Chemistry.CombustionAcoustics.acousticModeEnergy_sub_eq_integral
    (γ := 2) (pbar := 1) (ρ := 1) (L := Real.pi) (r := 3) (H := 0)
    (by norm_num) (by norm_num) Real.pi_pos
    (A := fun s : ℝ => 2 * Real.exp (-s)) (B := fun s : ℝ => Real.exp (-s))
    (A' := fun t : ℝ => -2 * Real.exp (-t))
    (B' := fun t : ℝ => -Real.exp (-t)) 0 1 hA hB
    (fun t _ => by
      show -2 * Real.exp (-t) =
        -2 * 1 * (Real.pi / Real.pi) * Real.exp (-t) + (2 - 1) * 0
      rw [div_self Real.pi_ne_zero]
      ring)
    (fun t _ => by
      show (1 : ℝ) * (-Real.exp (-t)) =
        (Real.pi / Real.pi) * (2 * Real.exp (-t)) - 3 * Real.exp (-t)
      rw [div_self Real.pi_ne_zero]
      ring)
  rw [h]
  have hF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => -(Real.exp (-2 * s)) / 2)
        (Real.exp (-2 * t)) t := by
    intro t _
    have h2 := ((hasDerivAt_id t).const_mul (-2 : ℝ)).exp
    have h3 := h2.const_mul (-1 / 2 : ℝ)
    convert h3 using 1
    · first
      | (funext s; simp only [id_eq]; congr 1; ring)
      | (simp only [id_eq]; ring_nf)
    · first
      | (funext s; simp only [id_eq]; congr 1; ring)
      | (simp only [id_eq]; ring_nf)
  have hint : (∫ t in (0 : ℝ)..(1 : ℝ), Real.exp (-2 * t)) =
      (1 - Real.exp (-2)) / 2 := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable
        0 1)
    rw [hi]
    norm_num
    ring
  have e : (∫ t in (0 : ℝ)..(1 : ℝ),
      (Real.pi * (2 - 1) * (2 * Real.exp (-t)) * 0 / (2 * 2 * 1) -
        3 * Real.pi * (Real.exp (-t)) ^ 2 / 2)) =
      ∫ t in (0 : ℝ)..(1 : ℝ), (-(3 * Real.pi / 2) * Real.exp (-2 * t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    have hsq : (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    show Real.pi * (2 - 1) * (2 * Real.exp (-t)) * 0 / (2 * 2 * 1) -
        3 * Real.pi * (Real.exp (-t)) ^ 2 / 2 =
      -(3 * Real.pi / 2) * Real.exp (-2 * t)
    rw [hsq]
    ring
  rw [e, intervalIntegral.integral_const_mul, hint]
  ring

/-- The lower fold for `Ta = 1`, `B = 5`: stationary at
`(5 - √(25 - 20)) / 2`, above `Ta`. -/
example : deriv (Chemistry.CombustionAcoustics.critRatio 1 5)
    ((5 - Real.sqrt (5 ^ 2 - 4 * 5 * 1)) / 2) = 0 :=
  (Chemistry.CombustionAcoustics.critRatio_two_folds one_pos (by norm_num)).1

example : (1 : ℝ) < (5 - Real.sqrt (5 ^ 2 - 4 * 5 * 1)) / 2 :=
  (Chemistry.CombustionAcoustics.critRatio_two_folds one_pos (by norm_num)).2.2.1

/-- No stationary point above `Ta = 1` for `B = 3 < 4`; checked at
`T = 2`. -/
example : deriv (Chemistry.CombustionAcoustics.critRatio 1 3) 2 ≠ 0 :=
  Chemistry.CombustionAcoustics.critRatio_no_critical_of_lt one_pos
    (by norm_num) (by norm_num)

/-- At `B = 4 * Ta` the unique stationary point above `Ta = 1` is
`T = 2`, and the second derivative vanishes there. -/
example : deriv (Chemistry.CombustionAcoustics.critRatio 1 (4 * 1)) 2 = 0 :=
  (Chemistry.CombustionAcoustics.critRatio_degenerate_fold one_pos
    (by norm_num)).mpr (by norm_num)

example : deriv (fun s : ℝ =>
    deriv (Chemistry.CombustionAcoustics.critRatio 1 (4 * 1)) s) (2 * 1) = 0 :=
  Chemistry.CombustionAcoustics.critRatio_degenerate_fold_second one_pos

/-- Ordinary folds are nondegenerate: both second derivatives are
nonzero for `Ta = 1`, `B = 5`. -/
example : deriv (fun s : ℝ =>
    deriv (Chemistry.CombustionAcoustics.critRatio 1 5) s)
    ((5 - Real.sqrt (5 ^ 2 - 4 * 5 * 1)) / 2) ≠ 0 :=
  (Chemistry.CombustionAcoustics.critRatio_two_folds_nondegenerate one_pos
    (by norm_num)).1

example : deriv (fun s : ℝ =>
    deriv (Chemistry.CombustionAcoustics.critRatio 1 5) s)
    ((5 + Real.sqrt (5 ^ 2 - 4 * 5 * 1)) / 2) ≠ 0 :=
  (Chemistry.CombustionAcoustics.critRatio_two_folds_nondegenerate one_pos
    (by norm_num)).2

/-! ## C. Frank-Kamenetskii criticality and box exit -/

section FrankKamenetskii

open Chemistry.CombustionAcoustics

/-- Fixture `δ = 1`: supercritical with growth slope `1 + log 1 = 1`, and a solution from
`θ₀ = 0` leaves the box `[0, 10]` through `10` by time `10`. -/
example :
    Real.exp (-1) < 1 ∧ 1 + Real.log 1 = (1 : ℝ) ∧
      ∃ τ : ℝ, 0 < τ ∧ τ ≤ 10 ∧
        ∃ θ : ℝ → ℝ, θ 0 = 0 ∧ θ τ = 10 ∧ (∀ s ∈ Set.Icc 0 τ, θ s ∈ Set.Icc 0 10) ∧
          ∀ s ∈ Set.Icc 0 τ, HasDerivWithinAt θ (fkField 1 (θ s)) (Set.Icc 0 τ) s := by
  have hexp1 : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  refine ⟨hexp1, ?_, ?_⟩
  · rw [Real.log_one]
    norm_num
  · obtain ⟨τ, hτpos, hτle, θ, h0, hτ, hbox, hode⟩ :=
      fk_exists_box_exit (δ := 1) (a := 0) (b := 10) (θ₀ := 0) hexp1 (le_refl 0) (by norm_num)
    refine ⟨τ, hτpos, ?_, θ, h0, hτ, hbox, hode⟩
    rw [Real.log_one] at hτle
    norm_num at hτle
    exact hτle

/-- Contrast, not a transfer: with `G = exp 1`, `H = B = Ta = 1` the exponential approximation
at ambient has `δ = G * B * exp (-B / Ta) / (H * Ta ^ 2) = 1`, which has no equilibrium, but the
exact Arrhenius rate has an equilibrium in `(1, 1 + exp 1)`. -/
example :
    Real.exp 1 * 1 * Real.exp (-1 / 1) / (1 * 1 ^ 2) = 1 ∧
      (¬ ∃ θ : ℝ, 0 ≤ θ ∧ fkField 1 θ = 0) ∧
      ∃ T ∈ Set.Ioo (1 : ℝ) (1 + Real.exp 1), arrheniusRate (Real.exp 1) 1 1 1 T = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : Real.exp 1 * Real.exp (-1) = 1 := by
      have e : (1 : ℝ) + -1 = 0 := by norm_num
      calc Real.exp 1 * Real.exp (-1) = Real.exp ((1 : ℝ) + -1) := (Real.exp_add _ _).symm
        _ = Real.exp 0 := by rw [e]
        _ = 1 := Real.exp_zero
    have h1 : (-1 : ℝ) / 1 = -1 := by norm_num
    have h2 : (1 : ℝ) * 1 ^ 2 = 1 := by norm_num
    rw [h1, h2, div_one, mul_one]
    exact h
  · intro hex
    have hle := (exists_nonneg_fkField_eq_zero_iff (zero_lt_one : (0 : ℝ) < 1)).mp hex
    have hlt : Real.exp (-1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  · have h := arrhenius_equilibrium_exists (G := Real.exp 1) (H := 1) (B := 1) (Ta := 1)
      (Real.exp_pos 1) zero_lt_one zero_lt_one zero_lt_one
    obtain ⟨T, hTmem, hTeq⟩ := h
    refine ⟨T, ?_, hTeq⟩
    simpa using hTmem

/-- Subcritical `δ = exp (-2) < exp (-1)`: the criterion gives a nonnegative equilibrium. -/
example : ∃ θ : ℝ, 0 ≤ θ ∧ fkField (Real.exp (-2)) θ = 0 :=
  (exists_nonneg_fkField_eq_zero_iff (Real.exp_pos _)).2
    (Real.exp_le_exp.2 (by norm_num))

/-- Critical `δ = exp (-1)`: the only equilibrium is `θ = 1`. -/
example (θ : ℝ) (h : fkField (Real.exp (-1)) θ = 0) : θ = 1 :=
  fkField_critical_tangency.2.2 θ h

/-- Supercritical `δ = 1`: the field is at least `1`, and the slope `1 + log 1` is positive. -/
example (θ : ℝ) : 1 ≤ fkField 1 θ ∧ 0 < 1 + Real.log 1 := by
  have h := one_add_log_le_fkField one_pos θ
  rw [Real.log_one, add_zero] at h
  exact ⟨h, (one_add_log_pos_iff one_pos).2 (by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this)⟩

/-- Growth and time-in-box bounds for `δ = 1`: a solution from `0` on `[0, t]` is at least `t`
at time `t`, and if it stays at or below `10` then `t ≤ 10`. -/
example {t : ℝ} (ht : 0 ≤ t) {θ : ℝ → ℝ} (h0 : θ 0 = 0)
    (hθ : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt θ (fkField 1 (θ s)) (Set.Icc 0 t) s)
    (hb : ∀ s ∈ Set.Icc 0 t, θ s ≤ 10) :
    t ≤ θ t ∧ t ≤ 10 := by
  have hlow := fk_solution_lower_bound one_pos ht hθ
  have hδ : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  have htime := fk_time_le_of_le hδ ht hθ hb
  rw [Real.log_one, add_zero, h0] at hlow htime
  constructor
  · linarith
  · simpa using htime

end FrankKamenetskii
