/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ScalarEnergyBalanceAttraction
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Tests for local attraction with heat capacity two -/

open EarthScience Filter Set
open scoped Topology

/-- Net flux with slope `-1` near three and a jump at four. -/
private noncomputable def flux (u : ℝ) : ℝ := if u < 4 then 3 - u else 100

private lemma flux_near : flux =ᶠ[𝓝 3] (fun u : ℝ => 3 - u) := by
  filter_upwards [Iio_mem_nhds (show (3 : ℝ) < 4 by norm_num)] with u hu
  exact ite_eq_left hu

private lemma flux_smooth : ContDiffAt ℝ 1 flux 3 :=
  (contDiffAt_const.sub contDiffAt_id).congr_of_eventuallyEq flux_near

private lemma flux_zero : flux 3 = 0 := by norm_num [flux]

private lemma flux_slope : deriv flux 3 < 0 := by
  have h := ((hasDerivAt_id (3 : ℝ)).const_sub 3).congr_of_eventuallyEq flux_near
  rw [h.deriv]
  norm_num

-- The flux jumps at 4. Construct a trajectory from a genuinely non-equilibrium start,
-- and extract its bound and the right derivative at the initial time without assuming a solution.
example : ∃ (u K α : ℝ) (T : ℝ → ℝ), 3 < u ∧ 0 < K ∧ 0 < α ∧ T 0 = u ∧
    IsIntegralCurveOn T (fun _ y => flux y / 2) (Ici 0) ∧
    HasDerivWithinAt T (flux u / 2) (Ici 0) 0 ∧
    ∀ t ≥ 0, |T t - 3| ≤ K * Real.exp (-(α * t)) * |u - 3| := by
  obtain ⟨δ, K, α, hδ, hK, hα, solve⟩ := local_attraction_in_a_scalar_energy_balance_model
    (C := 2) (by norm_num) flux_smooth flux_zero flux_slope
  have hu : |(3 + δ / 2) - 3| < δ := by
    rw [add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  obtain ⟨T, h₀, hODE, hbound, -⟩ := solve _ hu
  exact ⟨_, K, α, T, by linarith, hK, hα, h₀, hODE, h₀ ▸ hODE 0 le_rfl, hbound⟩

-- At equilibrium, a competitor may even jump from the left at zero. Uniqueness compares
-- trajectories on the forward half-line; no left derivative or negative-time value is needed.
example : ∃ T : ℝ → ℝ, T 0 = 3 ∧ IsIntegralCurveOn T (fun _ y => flux y / 2) (Ici 0) ∧
    EqOn (fun t : ℝ => if 0 ≤ t then 3 else 7) T (Ici 0) := by
  obtain ⟨δ, _, _, hδ, _, _, solve⟩ := local_attraction_in_a_scalar_energy_balance_model
    (C := 2) (by norm_num) flux_smooth flux_zero flux_slope
  obtain ⟨T, h₀, hODE, -, hunique⟩ := solve 3 (by simpa using hδ)
  refine ⟨T, h₀, hODE, hunique _ (by simp) ?_⟩
  intro t ht
  simp only [ite_eq_left (show 0 ≤ t from ht), flux_zero, zero_div]
  exact (hasDerivWithinAt_const t (Ici 0) (3 : ℝ)).congr_of_mem (fun _ hs => ite_eq_left hs) ht
