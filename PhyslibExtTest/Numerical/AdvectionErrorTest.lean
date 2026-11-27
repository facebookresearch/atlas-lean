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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Periodic upwind step and traveling-wave checks

Concrete consumers of `PhyslibExt.Numerical.AdvectionError`: a nonuniform nonnegative state on
three cells at Courant number `1/2`, and the state `(1, 0)` on two cells at Courant number `3/2`,
where the step conserves the total but produces a negative cell; and the traveling wave
`2 + sin(2π (x - t))`, with its values, slope, period, positivity and derivative bounds, together
with the failure of positivity at mean `1`; and the same wave sampled on four cells at Courant
number `1/2`, with a nonzero truncation error at the wrapped node inside the truncation bound,
the accumulated-error bound after eight steps, and the loss of max-norm nonexpansiveness at
Courant number `3/2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Below and above the CFL limit
- B. A positive traveling wave
- C. Nodal error of the upwind update for the wave

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

/-! ## C. Nodal error of the upwind update for the wave -/

/-- Nonzero amplitude, speed and spacing: `c₀ = 2`, `a = 1`, `v = 1`, `L = 1` on four cells
(`dx = 1 / 4`) with `dt = 1 / 8`, so `ν = v * dt / dx = 1 / 2`. At the wrapped node `j = 0`,
whose upstream sample is the last node `x = 3 / 4`, the first-step truncation error is
`1 / 2 - √2 / 2 ≠ 0`, inside the bound `dt * M * (v² dt + v dx) / 2 = 3 π² / 32`. -/
example :
    (1 : ℝ) * (1 / 8) / (1 / ((4 : ℕ) : ℝ)) = 1 / 2 ∧
      sampledWave 2 1 1 1 (1 / 8) 4 1 0 -
          ((1 - 1 / 2) * sampledWave 2 1 1 1 (1 / 8) 4 0 0 +
            1 / 2 * sampledWave 2 1 1 1 (1 / 8) 4 0 (0 - 1)) = 1 / 2 - √2 / 2 ∧
      1 / 2 - √2 / 2 ≠ (0 : ℝ) ∧
      (1 / 8 : ℝ) * (|1| * (2 * Real.pi / 1) ^ 2) *
          (1 ^ 2 * (1 / 8) + 1 * (1 / ((4 : ℕ) : ℝ))) / 2 = 3 * Real.pi ^ 2 / 32 ∧
      |1 / 2 - √2 / 2| ≤ 3 * Real.pi ^ 2 / (32 : ℝ) := by
  have h1 : (1 : ℝ) * (1 / 8) / (1 / ((4 : ℕ) : ℝ)) = 1 / 2 := by norm_num
  have hw10 : sampledWave 2 1 1 1 (1 / 8) 4 1 0 = 2 - √2 / 2 := by
    unfold sampledWave
    rw [ZMod.val_zero]
    unfold travelingWave
    have harg : 2 * Real.pi * ((((0 : ℕ) : ℝ)) * (1 / ((4 : ℕ) : ℝ))
        - 1 * (((1 : ℕ) : ℝ) * (1 / 8))) / 1 = -(Real.pi / 4) := by
      push_cast
      ring
    rw [harg, Real.sin_neg, Real.sin_pi_div_four]
    ring
  have hw00 : sampledWave 2 1 1 1 (1 / 8) 4 0 0 = 2 := by
    unfold sampledWave
    rw [ZMod.val_zero]
    unfold travelingWave
    have harg : 2 * Real.pi * ((((0 : ℕ) : ℝ)) * (1 / ((4 : ℕ) : ℝ))
        - 1 * (((0 : ℕ) : ℝ) * (1 / 8))) / 1 = 0 := by
      push_cast
      ring
    rw [harg, Real.sin_zero]
    ring
  have hw0m1 : sampledWave 2 1 1 1 (1 / 8) 4 0 (0 - 1) = 1 := by
    rw [sampledWave_sub_one (show (1 : ℝ) ≠ 0 by norm_num) 2 1 1 (1 / 8) 0 0]
    rw [ZMod.val_zero]
    unfold travelingWave
    have harg : 2 * Real.pi * ((((0 : ℕ) : ℝ)) * (1 / ((4 : ℕ) : ℝ))
        - 1 / ((4 : ℕ) : ℝ) - 1 * (((0 : ℕ) : ℝ) * (1 / 8))) / 1 = -(Real.pi / 2) := by
      push_cast
      ring
    rw [harg, Real.sin_neg, Real.sin_pi_div_two]
    ring
  have h2 : sampledWave 2 1 1 1 (1 / 8) 4 1 0 -
        ((1 - 1 / 2) * sampledWave 2 1 1 1 (1 / 8) 4 0 0 +
          1 / 2 * sampledWave 2 1 1 1 (1 / 8) 4 0 (0 - 1)) = 1 / 2 - √2 / 2 := by
    rw [hw10, hw00, hw0m1]
    ring
  have hsq : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hsqrt2 : 1 < √2 := by nlinarith [hsq, hnn]
  have h3 : 1 / 2 - √2 / 2 ≠ (0 : ℝ) := by
    intro hcon
    linarith [hcon, hsqrt2]
  have h4 : (1 / 8 : ℝ) * (|1| * (2 * Real.pi / 1) ^ 2) *
      (1 ^ 2 * (1 / 8) + 1 * (1 / ((4 : ℕ) : ℝ))) / 2 = 3 * Real.pi ^ 2 / 32 := by
    simp only [abs_one, Nat.cast_ofNat]
    ring
  have h5 : |1 / 2 - √2 / 2| ≤ 3 * Real.pi ^ 2 / (32 : ℝ) := by
    have hneg : (1 : ℝ) / 2 - √2 / 2 < 0 := by linarith [hsqrt2]
    rw [abs_of_neg hneg]
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by
      have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi)
      rw [Real.cos_pi] at hcos
      linarith [hcos]
    have hsq2ub : √2 ≤ 7 / 4 := by nlinarith [hsq, hnn]
    linarith [hpi2, hsq2ub]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- CFL failure: at `ν = 3 / 2` the update is not nonexpansive. On two cells it maps the
alternating state `(1, -1)`, of maximum norm `1`, to `(-2, 2)`, of maximum norm `2`. -/
example :
    ‖fun j : ZMod 2 => if j = 0 then (1 : ℝ) else -1‖ = 1 ∧
      ‖fun j : ZMod 2 => (1 - 3 / 2) * (if j = 0 then (1 : ℝ) else -1) +
        3 / 2 * (if j - 1 = 0 then (1 : ℝ) else -1)‖ = 2 := by
  have hall : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  have hf1 : ‖fun j : ZMod 2 => if j = 0 then (1 : ℝ) else -1‖ = 1 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro j
      show ‖(if j = 0 then (1 : ℝ) else -1)‖ ≤ 1
      split_ifs with hj
      · rw [Real.norm_eq_abs]; norm_num
      · rw [Real.norm_eq_abs]; norm_num
    · have h0 := norm_le_pi_norm (fun j : ZMod 2 => if j = 0 then (1 : ℝ) else -1) 0
      have h0' : ‖(if (0 : ZMod 2) = 0 then (1 : ℝ) else -1)‖ ≤
          ‖fun j : ZMod 2 => if j = 0 then (1 : ℝ) else -1‖ := h0
      have hif : (if (0 : ZMod 2) = 0 then (1 : ℝ) else -1) = 1 := by simp
      rw [hif, Real.norm_eq_abs] at h0'
      norm_num at h0'
      exact h0'
  have hg2 : ‖fun j : ZMod 2 => (1 - 3 / 2) * (if j = 0 then (1 : ℝ) else -1) +
      3 / 2 * (if j - 1 = 0 then (1 : ℝ) else -1)‖ = 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro j
      rcases hall j with rfl | rfl
      · show ‖(1 - 3 / 2) * (if (0 : ZMod 2) = 0 then (1 : ℝ) else -1) +
            3 / 2 * (if (0 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1)‖ ≤ 2
        have e1 : (if (0 : ZMod 2) = 0 then (1 : ℝ) else -1) = 1 := by simp
        have e2 : (if (0 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1) = -1 := by simp
        rw [e1, e2, Real.norm_eq_abs]
        norm_num
      · show ‖(1 - 3 / 2) * (if (1 : ZMod 2) = 0 then (1 : ℝ) else -1) +
            3 / 2 * (if (1 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1)‖ ≤ 2
        have e1 : (if (1 : ZMod 2) = 0 then (1 : ℝ) else -1) = -1 := by simp
        have e2 : (if (1 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1) = 1 := by simp
        rw [e1, e2, Real.norm_eq_abs]
        norm_num
    · have h1 := norm_le_pi_norm (fun j : ZMod 2 => (1 - 3 / 2)
          * (if j = 0 then (1 : ℝ) else -1) + 3 / 2 * (if j - 1 = 0 then (1 : ℝ) else -1)) 1
      have h1' : ‖(1 - 3 / 2) * (if (1 : ZMod 2) = 0 then (1 : ℝ) else -1) +
          3 / 2 * (if (1 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1)‖ ≤
          ‖fun j : ZMod 2 => (1 - 3 / 2) * (if j = 0 then (1 : ℝ) else -1) +
            3 / 2 * (if j - 1 = 0 then (1 : ℝ) else -1)‖ := h1
      have e1 : (if (1 : ZMod 2) = 0 then (1 : ℝ) else -1) = -1 := by simp
      have e2 : (if (1 - 1 : ZMod 2) = 0 then (1 : ℝ) else -1) = 1 := by simp
      rw [e1, e2, Real.norm_eq_abs] at h1'
      rw [show (1 - 3 / 2) * (-1 : ℝ) + 3 / 2 * 1 = 2 by norm_num] at h1'
      rw [show |(2 : ℝ)| = 2 by norm_num] at h1'
      exact h1'
  exact ⟨hf1, hg2⟩

/-- The accumulated-error bound on the same grid (`ν = 1 / 2`): for every numerical solution of
the upwind recurrence, after `8` steps of length `1 / 8` (final time `T = 1`) the nodal error has
grown by at most `T * M * (v² dt + v dx) / 2 = 3 π² / 4`. -/
example (u : ℕ → ZMod 4 → ℝ)
    (hu : ∀ k j, u (k + 1) j = (1 - 1 / 2) * u k j + 1 / 2 * u k (j - 1)) :
    ‖fun j => u 8 j - sampledWave 2 1 1 1 (1 / 8) 4 8 j‖ ≤
      ‖fun j => u 0 j - sampledWave 2 1 1 1 (1 / 8) 4 0 j‖ + 3 * Real.pi ^ 2 / 4 := by
  have hν : (1 : ℝ) * (1 / 8) / (1 / ((4 : ℕ) : ℝ)) = 1 / 2 := by norm_num
  have hu' : ∀ k j, u (k + 1) j = (1 - (1 : ℝ) * (1 / 8) / (1 / ((4 : ℕ) : ℝ))) * u k j +
      (1 : ℝ) * (1 / 8) / (1 / ((4 : ℕ) : ℝ)) * u k (j - 1) := by
    intro k j
    rw [hν]
    exact hu k j
  have h := upwind_error_le_of_mul_le (c₀ := 2) (a := 1) (ncells := 4) (v := 1) (L := 1)
    (dt := 1 / 8) one_pos (by norm_num) (by rw [hν]; norm_num) (by rw [hν]; norm_num) u hu' 8
    (T := 1) (by norm_num)
  have hb : (1 : ℝ) * (|(1 : ℝ)| * (2 * Real.pi / 1) ^ 2) *
      ((1 : ℝ) ^ 2 * (1 / 8) + 1 * (1 / ((4 : ℕ) : ℝ))) / 2 = 3 * Real.pi ^ 2 / 4 := by
    rw [abs_one]
    push_cast
    ring
  rw [hb] at h
  exact h
