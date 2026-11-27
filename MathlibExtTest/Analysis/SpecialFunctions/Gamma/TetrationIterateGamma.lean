/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.TetrationIterateGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

open MetaMathlibExt Real Filter Topology

-- The base 4 lies above a nontrivial Gamma fixed point.
example : ∃ z ∈ Set.Ioo (3 : ℝ) 4, Gamma z = z := by
  have hpos : Set.Icc (3 : ℝ) 4 ⊆ Set.Ioi 0 := fun _ hx =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hx.1
  have hcont : ContinuousOn (fun x : ℝ => Gamma x - x) (Set.Icc 3 4) :=
    (differentiableOn_Gamma_Ioi.continuousOn.mono hpos).sub continuousOn_id
  have hsign : (0 : ℝ) ∈ Set.Ioo (Gamma 3 - 3) (Gamma 4 - 4) := by
    norm_num [Set.mem_Ioo, Gamma_ofNat_eq_factorial, Nat.factorial]
  obtain ⟨z, hz, heq⟩ := intermediate_value_Ioo (by norm_num) hcont hsign
  exact ⟨z, hz, sub_eq_zero.mp heq⟩

-- At height one, the tower is the base and the Gamma iterate is one application.
example {z b : ℝ} (hz : 1 < z) (hΓz : Gamma z = z) (hb : z < b) :
    ∃ x : ℕ → ℝ, b = Gamma (x 1) ∧ (∃ L : ℝ, Tendsto x atTop (𝓝 L)) ∧
      ∃ M : ℕ, x (M + 2) < x (M + 1) := by
  obtain ⟨x, hx, hconv, M, hanti⟩ := exists_tetration_eq_iterate_Gamma hz hΓz hb
  refine ⟨x, ?_, hconv, M, ?_⟩
  · have h1 := hx 1 le_rfl
    simpa using h1
  · exact hanti (Set.mem_Ici.mpr (Nat.le_succ M)) (Set.mem_Ici.mpr (by omega))
      (by omega)

-- At height two, the tower is `b ^ b` and the Gamma iterate is two applications.
example {z b : ℝ} (hz : 1 < z) (hΓz : Gamma z = z) (hb : z < b) :
    ∃ x : ℕ → ℝ, b ^ b = Gamma (Gamma (x 2)) ∧ (∃ L : ℝ, Tendsto x atTop (𝓝 L)) := by
  obtain ⟨x, hx, hconv, -, -⟩ := exists_tetration_eq_iterate_Gamma hz hΓz hb
  refine ⟨x, ?_, hconv⟩
  have h2 := hx 2 (by norm_num)
  simpa [rpow_one] using h2
