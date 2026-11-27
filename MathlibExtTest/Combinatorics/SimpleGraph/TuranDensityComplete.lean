/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TuranDensityComplete
import Mathlib.Tactic.NormNum

/-!
# Tests for the Turán density of complete graphs

Mantel's density `π(K₃) = 1/2`, `π(K₄) = 2/3`, the degenerate case `π(K₂) = 0` (`r = 1`: every
graph with an edge contains `K₂`), and the lower bound on `t(4, 2) = 4`.
-/

open MathlibExt.Combinatorics.SimpleGraph.TuranDensityComplete _root_.SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.TuranDensityComplete

example : turanDensity (⊤ : SimpleGraph (Fin 3)) = 1 / 2 := by
  rw [turanDensity_completeGraph (r := 2) (by norm_num)]; norm_num

example : turanDensity (⊤ : SimpleGraph (Fin 4)) = 2 / 3 := by
  rw [turanDensity_completeGraph (r := 3) (by norm_num)]; norm_num

example : turanDensity (⊤ : SimpleGraph (Fin 2)) = 0 := by
  rw [turanDensity_completeGraph (r := 1) le_rfl]; norm_num

/-- `T(4, 2) = K_{2,2}` has `4` edges, and `(2 - 1)(4 ^ 2 - 2 ^ 2) = 12 ≤ 16 = 2 · 2 · 4`. -/
example : ((2 : ℕ) - 1 : ℝ) * ((4 : ℕ) ^ 2 - (2 : ℕ) ^ 2 : ℝ) ≤ 2 * (2 : ℕ) * (turanNumber 4 2 : ℝ) :=
  turanNumber_lower_bound (by norm_num) 4

example : turanNumber 4 2 = 4 := by rw [turanNumber_two]; norm_num

end MathlibExtTest.Combinatorics.SimpleGraph.TuranDensityComplete
