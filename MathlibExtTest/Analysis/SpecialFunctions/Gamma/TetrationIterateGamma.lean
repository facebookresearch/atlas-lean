/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Gamma.TetrationIterateGamma

open MetaMathlibExt Real Filter Topology

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
