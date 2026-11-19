/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Numerical.AdvectionError
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Periodic upwind step and traveling-wave checks

Concrete consumers of `PhyslibExt.Numerical.AdvectionError`: a nonuniform nonnegative state on
three cells at Courant number `1/2`, and the state `(1, 0)` on two cells at Courant number `3/2`,
where the step conserves the total but produces a negative cell; and the traveling wave
`2 + sin(2π (x - t))`, with its values, slope, period, positivity and derivative bounds, together
with the failure of positivity at mean `1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Below and above the CFL limit
- B. A positive traveling wave

## iv. References

- `PhyslibExt.Numerical.AdvectionError`
-/

open AdvectionError

/-! ## A. Below and above the CFL limit -/

/-- Nonuniform nonnegative fixture with Courant number `1/2`: three cells with values
`(1, 0, 2)`, `area = 2`, `dx = 1/2`, `v = 1` and `dt = 1/4`. The conservative upwind step gives
`(3/2, 1/2, 1)`, which is nonnegative, and the total mass is `3` before and after. -/
example :
    (1 : ℝ) * (1 / 4) / (1 / 2) = 1 / 2 ∧
      IsConservativeStep (n := 3) 2 (1 / 2) (1 / 4) (upwindFaceFlux 2 1 ![1, 0, 2])
        ![1, 0, 2] ![3 / 2, 1 / 2, 1] ∧
      (∀ i : ZMod 3, 0 ≤ (![3 / 2, 1 / 2, 1] : ZMod 3 → ℝ) i) ∧
      ∑ i : ZMod 3, 2 * (1 / 2) * (![1, 0, 2] : ZMod 3 → ℝ) i = 3 ∧
      ∑ i : ZMod 3, 2 * (1 / 2) * (![3 / 2, 1 / 2, 1] : ZMod 3 → ℝ) i = 3 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · unfold IsConservativeStep upwindFaceFlux
    intro i
    fin_cases i
    · have hmax : max (1 : ℝ) 0 = 1 := max_eq_left zero_le_one
      have hmin : min (1 : ℝ) 0 = 0 := min_eq_right zero_le_one
      rw [hmax, hmin]
      show (2 : ℝ) * (1 / 2) * (3 / 2) =
        2 * (1 / 2) * 1 + (1 / 4) * ((2 * (1 * 2 + 0 * 1)) - (2 * (1 * 1 + 0 * 0)))
      norm_num
    · have hmax : max (1 : ℝ) 0 = 1 := max_eq_left zero_le_one
      have hmin : min (1 : ℝ) 0 = 0 := min_eq_right zero_le_one
      rw [hmax, hmin]
      show (2 : ℝ) * (1 / 2) * (1 / 2) =
        2 * (1 / 2) * 0 + (1 / 4) * ((2 * (1 * 1 + 0 * 0)) - (2 * (1 * 0 + 0 * 2)))
      norm_num
    · have hmax : max (1 : ℝ) 0 = 1 := max_eq_left zero_le_one
      have hmin : min (1 : ℝ) 0 = 0 := min_eq_right zero_le_one
      rw [hmax, hmin]
      show (2 : ℝ) * (1 / 2) * 1 =
        2 * (1 / 2) * 2 + (1 / 4) * ((2 * (1 * 0 + 0 * 2)) - (2 * (1 * 2 + 0 * 1)))
      norm_num
  · intro i
    fin_cases i
    · show (0 : ℝ) ≤ 3 / 2
      norm_num
    · show (0 : ℝ) ≤ 1 / 2
      norm_num
    · show (0 : ℝ) ≤ (1 : ℝ)
      norm_num
  · change ∑ i : Fin 3, 2 * (1 / 2) * (![1, 0, 2] : Fin 3 → ℝ) i = 3
    rw [Fin.sum_univ_three]
    simp
    norm_num
  · change ∑ i : Fin 3, 2 * (1 / 2) * (![3 / 2, 1 / 2, 1] : Fin 3 → ℝ) i = 3
    rw [Fin.sum_univ_three]
    simp
    norm_num

/-- Invalid fixture above the CFL limit: two cells with values `(1, 0)`, `area = 1`, `dx = 1`,
`v = 3` and `dt = 1/2`, so the Courant number is `3/2`. The conservative upwind step gives
`(-1/2, 3/2)`: the total `1` is conserved, but the first cell is negative. -/
example :
    (3 : ℝ) * (1 / 2) / 1 = 3 / 2 ∧
      IsConservativeStep (n := 2) 1 1 (1 / 2) (upwindFaceFlux 1 3 ![1, 0]) ![1, 0]
        ![-1 / 2, 3 / 2] ∧
      ∑ i : ZMod 2, 1 * 1 * (![-1 / 2, 3 / 2] : ZMod 2 → ℝ) i =
        ∑ i : ZMod 2, 1 * 1 * (![1, 0] : ZMod 2 → ℝ) i ∧
      (![-1 / 2, 3 / 2] : ZMod 2 → ℝ) 0 < 0 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · unfold IsConservativeStep upwindFaceFlux
    intro i
    fin_cases i
    · have hmax : max (3 : ℝ) 0 = 3 := max_eq_left (by norm_num)
      have hmin : min (3 : ℝ) 0 = 0 := min_eq_right (by norm_num)
      rw [hmax, hmin]
      show (1 : ℝ) * 1 * (-1 / 2) =
        1 * 1 * 1 + (1 / 2) * ((1 * (3 * 0 + 0 * 1)) - (1 * (3 * 1 + 0 * 0)))
      norm_num
    · have hmax : max (3 : ℝ) 0 = 3 := max_eq_left (by norm_num)
      have hmin : min (3 : ℝ) 0 = 0 := min_eq_right (by norm_num)
      rw [hmax, hmin]
      show (1 : ℝ) * 1 * (3 / 2) =
        1 * 1 * 0 + (1 / 2) * ((1 * (3 * 1 + 0 * 0)) - (1 * (3 * 0 + 0 * 1)))
      norm_num
  · change (∑ i : Fin 2, 1 * 1 * (![-1 / 2, 3 / 2] : Fin 2 → ℝ) i) =
      (∑ i : Fin 2, 1 * 1 * (![1, 0] : Fin 2 → ℝ) i)
    simp only [Fin.sum_univ_two]
    simp
    norm_num
  · show ((-1 : ℝ) / 2) < 0
    norm_num

/-! ## B. A positive traveling wave -/

/-- Nonzero amplitude and moving phase: for `c₀ = 2`, `a = 1`, `v = 1` and `L = 1`, the value at
`x = 1/4` is `3` at time `0` and `2` at time `1/4`, and the slope at the origin is `2π ≠ 0`. -/
example :
    travelingWave 2 1 1 1 0 (1 / 4) = 3 ∧ travelingWave 2 1 1 1 (1 / 4) (1 / 4) = 2 ∧
      deriv (fun y => travelingWave 2 1 1 1 0 y) 0 = 2 * Real.pi := by
  have h1 : travelingWave 2 1 1 1 0 (1 / 4) = 3 := by
    simp only [travelingWave]
    have harg : 2 * Real.pi * (1 / 4 - 1 * 0) / 1 = Real.pi / 2 := by ring
    rw [harg, Real.sin_pi_div_two]
    norm_num
  have h2 : travelingWave 2 1 1 1 (1 / 4) (1 / 4) = 2 := by
    simp only [travelingWave]
    have harg : 2 * Real.pi * (1 / 4 - 1 * (1 / 4)) / 1 = 0 := by ring
    rw [harg, Real.sin_zero]
    norm_num
  have h3 : deriv (fun y => travelingWave 2 1 1 1 0 y) 0 = 2 * Real.pi := by
    have hder := (travelingWave_hasDerivAt_space 2 1 1 1 0 0).deriv
    rw [hder]
    have harg : 2 * Real.pi * (0 - 1 * 0) / 1 = 0 := by ring
    rw [harg, Real.cos_zero]
    norm_num
  exact ⟨h1, h2, h3⟩

/-- The traveling-wave lemmas at `c₀ = 2`, `a = 1`, `v = 1` and `L = 1`: the wave solves the
advection equation, has period `1`, stays positive, and both second derivatives are bounded by
`4 π²`; with mean `1` instead, the wave reaches a nonpositive value at every time. -/
example (t x : ℝ) :
    deriv (fun τ => travelingWave 2 1 1 1 τ x) t +
        1 * deriv (fun y => travelingWave 2 1 1 1 t y) x = 0 ∧
      travelingWave 2 1 1 1 t (x + 1) = travelingWave 2 1 1 1 t x ∧
      0 < travelingWave 2 1 1 1 t x ∧
      |iteratedDeriv 2 (fun y => travelingWave 2 1 1 1 t y) x| ≤ 4 * Real.pi ^ 2 ∧
      |iteratedDeriv 2 (fun τ => travelingWave 2 1 1 1 τ x) t| ≤ 4 * Real.pi ^ 2 ∧
      ∃ y, travelingWave 1 1 1 1 t y ≤ 0 := by
  refine ⟨travelingWave_advection 2 1 1 1 t x, travelingWave_periodic one_ne_zero 2 1 1 t x,
    travelingWave_pos (by norm_num) 1 1 t x, ?_, ?_,
    travelingWave_exists_nonpos one_ne_zero (by norm_num) 1 t⟩
  · calc |iteratedDeriv 2 (fun y => travelingWave 2 1 1 1 t y) x|
        ≤ |(1 : ℝ)| * (2 * Real.pi / 1) ^ 2 := travelingWave_space_bound 2 1 1 1 t x
      _ = 4 * Real.pi ^ 2 := by
        rw [abs_one]
        ring
  · calc |iteratedDeriv 2 (fun τ => travelingWave 2 1 1 1 τ x) t|
        ≤ (1 : ℝ) ^ 2 * (|(1 : ℝ)| * (2 * Real.pi / 1) ^ 2) :=
          travelingWave_time_bound 2 1 1 1 t x
      _ = 4 * Real.pi ^ 2 := by
        rw [abs_one]
        ring
