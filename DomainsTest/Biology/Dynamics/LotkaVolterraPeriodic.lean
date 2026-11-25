/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.LotkaVolterraPeriodic

/-!
# Tests for Lotka–Volterra periodic orbits

The examples exhibit a positive global solution with a least positive return time, verify
that the coexistence equilibrium solves the equations on all of `ℝ`, and show why the
non-equilibrium hypothesis is necessary for a least positive return time.
-/

open Domains.Biology.Dynamics.LotkaVolterra

namespace DomainsTest.Biology.Dynamics.LotkaVolterraPeriodic

example : ∃ x y : ℝ → ℝ, x 0 = 2 ∧ y 0 = 1 ∧
    (∀ t, HasDerivAt x (x t - x t * y t) t ∧
      HasDerivAt y (x t * y t - y t) t) ∧
    (∀ t, 0 < x t ∧ 0 < y t) ∧ ∃ T > (0 : ℝ),
      (∀ t, 0 ≤ t → x (t + T) = x t ∧ y (t + T) = y t) ∧
      (∀ s, 0 < s → s < T → (x s, y s) ≠ (x 0, y 0)) := by
  obtain ⟨x, y, hx0, hy0, hd, hp⟩ := exists_global_solution
    (α := 1) (β := 1) (γ := 1) (δ := 1) (x₀ := 2) (y₀ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hne : (x 0, y 0) ≠ ((1 : ℝ) / 1, (1 : ℝ) / 1) := by
    rw [hx0, hy0]
    norm_num
  have hper := exists_minimal_period (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t _ => (hd t).1) (fun t _ => (hd t).2) (hp 0).1 (hp 0).2 hne
  refine ⟨x, y, hx0, hy0, ?_, hp, hper⟩
  simpa only [one_mul] using hd

example {α β γ δ : ℝ} (_hα : 0 < α) (hβ : 0 < β) (_hγ : 0 < γ) (hδ : 0 < δ) :
    ∀ t : ℝ, HasDerivAt (fun _ : ℝ => γ / δ)
      (α * (γ / δ) - β * (γ / δ) * (α / β)) t ∧
      HasDerivAt (fun _ : ℝ => α / β)
      (δ * (γ / δ) * (α / β) - γ * (α / β)) t := by
  intro t
  constructor
  · convert hasDerivAt_const t (γ / δ) using 1
    field_simp
    ring
  · convert hasDerivAt_const t (α / β) using 1
    field_simp
    ring

example (α β γ δ : ℝ) : ¬ ∃ T > (0 : ℝ), ∀ s, 0 < s → s < T →
    ((fun _ : ℝ => γ / δ) s, (fun _ : ℝ => α / β) s) ≠
      ((fun _ : ℝ => γ / δ) 0, (fun _ : ℝ => α / β) 0) := by
  rintro ⟨T, hT, hmin⟩
  exact hmin (T / 2) (by linarith) (by linarith) rfl


end DomainsTest.Biology.Dynamics.LotkaVolterraPeriodic

#print axioms Domains.Biology.Dynamics.LotkaVolterra.pos_of_pos
#print axioms Domains.Biology.Dynamics.LotkaVolterra.exists_global_solution
#print axioms Domains.Biology.Dynamics.LotkaVolterra.eq_of_initial
#print axioms Domains.Biology.Dynamics.LotkaVolterra.exists_minimal_period
