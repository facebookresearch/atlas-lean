/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalErrorBudgets
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Numerical.PhysicalErrorBudgets`

* a nonunit bar `EA = 2`, `L = 3`, `q = 4` on two uniform cells, keeping both the coordinate and
  the amplitude scaling;
* the same bar: the amplitude is nonzero, the reconstruction is fixed at both ends, and the
  physical error obeys the mesh estimates;
* the zero load, treated without the inverse amplitude map;
* a body of heat capacity `500` coupled through `G = 5` to a bath at `300` (`τ = 100`), started
  at `350`: ten Euler steps of size `10` give `T_10 = 300 + 50 (9 / 10) ^ 10`, with
  `0 < |T_10 - T(100)| ≤ 5`;
* the same body: its trajectory solves `C T' = Q(T)` and the one-node storage law, while a node
  without a source keeps its temperature;
* the same body in minutes and in seconds, the step `τ / 10` entered in seconds against `τ` in
  minutes, and the unstable step `3 τ`.
-/

@[expose] public section

namespace PhyslibExtTest.Numerical.PhysicalErrorBudgets

open _root_.PhysicalErrorBudgets

/-! ## A. A nonunit bar on two cells -/

-- Nonunit fixture `EA = 2`, `L = 3`, `q = 4`, keeping both the coordinate and the amplitude
-- scaling: `α = 9`, quarter-point error `9 / 16`, energy `9 / 2`, squared `L²` error `81 / 160`.
example :
    barAmplitude 2 3 4 = 9 ∧ physicalError twoCells 2 3 4 (3 / 4) = 9 / 16 ∧
      ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 = 9 / 2 ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 = 81 / 160 := by
  have hα : barAmplitude 2 3 4 = 9 := by norm_num [barAmplitude]
  obtain ⟨h1, h2, h3⟩ := physicalError_twoCells (L := 3) (by norm_num) 2 4
  refine ⟨hα, ?_, ?_, ?_⟩
  · rw [h1, hα]
  · rw [h2, hα]
    norm_num
  · rw [h3, hα]
    norm_num

-- The amplitude of that bar is nonzero, so the normalization can be inverted.
example : barAmplitude 2 3 4 ≠ 0 :=
  (barAmplitude_ne_zero_iff (by norm_num) (by norm_num) 4).2 (by norm_num)

-- Its reconstruction is fixed at both ends of `[0, 3]`.
example : physicalP1 twoCells 2 3 4 0 = 0 ∧ physicalP1 twoCells 2 3 4 3 = 0 :=
  physicalP1_zero_and_length twoCells (by norm_num) 2 4

-- The energy and `L²` errors obey the physical mesh estimates.
example :
    ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 ≤
        2 / 3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 2) ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 ≤
        3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 4) :=
  ⟨integral_energy_physicalError_le_mesh twoCells (by norm_num) (by norm_num) 4,
    integral_sq_physicalError_le_mesh twoCells (by norm_num) 2 4⟩

/-! ## B. Zero load -/

-- With `q = 0` the error vanishes everywhere, and the inverse amplitude map does not recover
-- the unit profile.
example :
    physicalError twoCells 2 3 0 (3 / 4) = 0 ∧
      (barAmplitude 2 3 0)⁻¹ * Elasticity.PrismaticMembers.axialDisplacement 2 3 0 (3 * (1 / 2)) ≠
        unitProfile (1 / 2) :=
  ⟨(zero_load twoCells 2 3).2.2.2 (3 / 4), zero_load_inverse_ne 2 3⟩

/-! ## C. A body cooling in a fixed bath -/

/-- **Nonzero temperature excess.** A body of heat capacity `500` coupled through `G = 5` to a
bath at `300` has `τ = 100`. Started at `350` (`Δ = 50`), ten Euler steps of `10` (that is
`τ / 10`, in the same time unit as `τ`) give `T_10 = 300 + 50 (9 / 10) ^ 10`, and
`0 < |T_10 - T(100)| ≤ 5`. -/
lemma bathEuler_fixture {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j, X (j + 1) = bathEulerStep 500 5 300 10 (X j)) :
    X 10 = 300 + 50 * (9 / 10) ^ 10 ∧
      0 < |X 10 - bathTrajectory 500 5 300 50 100| ∧
      |X 10 - bathTrajectory 500 5 300 50 100| ≤ 5 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j, X (j + 1) =
      bathEulerStep 500 5 300 (thermalTimeConstant 500 5 / 10) (X j) := by
    intro j
    rw [hτ, hstep]
    norm_num
  have herr := bathEuler_tenStep_error (by norm_num) (by norm_num) h0' hstep'
  have hpos := bathEuler_tenStep_error_pos (by norm_num) (by norm_num) (by norm_num) h0' hstep'
  rw [hτ] at herr hpos
  refine ⟨bathEuler_closed_form (by norm_num) (by norm_num) h0' hstep' 10, hpos, ?_⟩
  norm_num at herr
  exact herr

/-! ## D. The bath trajectory and the one-node law -/

-- The trajectory of the body starts at `350` and satisfies `T' = Q(T) / C`: at `t = 0` the bath
-- power is `-5 · 50 = -250` and `T' = -250 / 500 = -1 / 2`; the stored heat `500 T` has the rate
-- `Q(T) = -250` there.
example :
    bathTrajectory 500 5 300 50 0 = 350 ∧
      HasDerivAt (bathTrajectory 500 5 300 50) (-1 / 2) 0 ∧
      HasDerivAt (fun s => 500 * bathTrajectory 500 5 300 50 s) (-250) 0 := by
  obtain ⟨h0, hd⟩ := bathTrajectory_solves (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50
  have hQ : bathPower 5 300 (bathTrajectory 500 5 300 50 0) = -250 := by
    rw [h0]
    norm_num [bathPower]
  refine ⟨by rw [h0]; norm_num, ?_, ?_⟩
  · have h := hd 0
    rw [hQ] at h
    convert h using 1
    norm_num
  · have h := bathTrajectory_storage (C := 500) (G := 5) (by norm_num) (by norm_num) 300 50 0
    rwa [hQ] at h

-- A node of capacity `500` without a source (`500 T' = 0`) keeps its temperature up to `t = 1000`,
-- while the body coupled to the bath has left its initial temperature by then.
example {T dT : ℝ → ℝ} (hT : ∀ t, HasDerivAt T (dT t) t) (hbal : ∀ t, 500 * dT t = 0) :
    T 1000 = T 0 ∧ bathTrajectory 500 5 300 50 1000 ≠ bathTrajectory 500 5 300 50 0 := by
  refine ⟨oneNode_noSource_const (by norm_num) hT hbal 1000, ?_⟩
  have h : Real.exp (-1000 / thermalTimeConstant 500 5) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num [thermalTimeConstant])
  intro heq
  simp only [bathTrajectory, neg_zero, zero_div, Real.exp_zero, mul_one] at heq
  linarith

/-! ## E. Time units and the unstable step -/

-- The same body in minutes and in seconds: with the conductance `300` per minute, `τ = 5 / 3`
-- minutes; in seconds (`k = 60`) the conductance is `300 / 60 = 5` per second and
-- `τ = 60 · (5 / 3) = 100`. The step `τ / 10`, `1 / 6` minute or `10` seconds, takes the body
-- from `350` to `345` in both units.
example :
    thermalTimeConstant 500 (300 / 60) = 60 * thermalTimeConstant 500 300 ∧
      thermalTimeConstant 500 300 = 5 / 3 ∧
      bathEulerStep 500 (300 / 60) 300 (60 * (1 / 6)) 350 =
        bathEulerStep 500 300 300 (1 / 6) 350 ∧
      bathEulerStep 500 300 300 (1 / 6) 350 = 345 := by
  obtain ⟨hτ, hstep⟩ := bathEulerStep_timeUnit (by norm_num : (0 : ℝ) < 60) 500 300 300 (1 / 6) 350
  exact ⟨hτ, by norm_num [thermalTimeConstant], hstep, by norm_num [bathEulerStep, bathPower]⟩

-- Mismatched units: with `τ = 5 / 3` minutes, the step `τ / 10` entered as its value in seconds,
-- `10`, is `60` times too large. It multiplies the excess `50` by `-5`: the body at `350` jumps to
-- `50`, far below the bath at `300`, instead of moving to `345`.
example : bathEulerStep 500 300 300 10 350 = 50 ∧ bathEulerStep 500 300 300 (1 / 6) 350 = 345 := by
  have h := bathEulerStep_minutes_seconds (C := 500) (G := 300) (by norm_num) (by norm_num) 300 50
  have hdt : (60 : ℝ) * (thermalTimeConstant 500 300 / 10) = 10 := by
    norm_num [thermalTimeConstant]
  rw [hdt] at h
  refine ⟨?_, by norm_num [bathEulerStep, bathPower]⟩
  rw [show (350 : ℝ) = 300 + 50 by norm_num, h]
  norm_num

-- The unstable step of the stable bath: with `τ = 100`, the step `3 τ = 300` multiplies the excess
-- by `-2`, giving `350`, `200`, `500`, ..., so after ten steps the excess is `2 ^ 10 · 50 = 51200`,
-- while the exact excess `50 exp (-t / 100)` never exceeds `50`.
example {X : ℕ → ℝ} (h0 : X 0 = 350)
    (hstep : ∀ j, X (j + 1) = bathEulerStep 500 5 300 300 (X j)) :
    X 1 = 200 ∧ X 2 = 500 ∧ |X 10 - 300| = 51200 ∧
      |bathTrajectory 500 5 300 50 1000 - 300| ≤ 50 := by
  have hτ : thermalTimeConstant 500 5 = 100 := by norm_num [thermalTimeConstant]
  have h0' : X 0 = 300 + 50 := by rw [h0]; norm_num
  have hstep' : ∀ j, X (j + 1) =
      bathEulerStep 500 5 300 (3 * thermalTimeConstant 500 5) (X j) := by
    intro j
    rw [hτ, hstep]
    norm_num
  obtain ⟨hexact, hX⟩ := bathEuler_threeTau (by norm_num) (by norm_num) h0' hstep'
  refine ⟨?_, ?_, ?_, (hexact 1000 (by norm_num)).trans_eq (by norm_num)⟩
  · rw [(hX 1).1]
    norm_num
  · rw [(hX 2).1]
    norm_num
  · rw [(hX 10).2]
    norm_num

end PhyslibExtTest.Numerical.PhysicalErrorBudgets

end
