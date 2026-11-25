/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TuranDensityChromatic

@[expose] public section

open SimpleGraph MathlibExt.Combinatorics.SimpleGraph.TuranDensityChromatic

namespace MathlibExtTest.Combinatorics.SimpleGraph.TuranDensityChromatic

/-- `T(7, 3)` is properly coloured by residues mod `3`. -/
example : (turanGraph 7 3).Colorable 3 := turanGraph_colorable 7 (by norm_num)

/-- The triangle has chromatic number `3`, so its Turán density is at least `1/2` (Mantel). -/
example : 1 - 1 / ((2 : ℕ) : ℝ) ≤ turanDensity (⊤ : SimpleGraph (Fin 3)) :=
  one_sub_inv_le_turanDensity_of_chromaticNumber _ (by norm_num) (by simp; rfl)

/-- `K₄` is not `2`-colourable, so `ex(n, K₃) ≤ ex(n, K₄)`: the Turán graph `T(n, 2)` avoids
`K₄`. -/
example (n : ℕ) : extremalNumber n (⊤ : SimpleGraph (Fin 3)) ≤
    extremalNumber n (⊤ : SimpleGraph (Fin 4)) :=
  extremalNumber_top_le _ (by norm_num) (fun h => by
    have := h.chromaticNumber_le
    simp at this
    exact absurd this (by decide)) n

/-- The general formula recovers `π(K₄) = 2/3`. -/
example : turanDensity (⊤ : SimpleGraph (Fin 4)) = 1 - 1 / ((3 : ℕ) : ℝ) :=
  turanDensity_eq_one_sub_inv_of_chromaticNumber _ (by norm_num) (by simp; rfl)

/-- The octahedron `K_3(2)` has Turán density at most `1/2`. -/
example : turanDensity (completeEquipartiteGraph (2 + 1) 2) ≤ 1 - 1 / ((2 : ℕ) : ℝ) :=
  turanDensity_completeEquipartiteGraph_le (by norm_num) 2

end MathlibExtTest.Combinatorics.SimpleGraph.TuranDensityChromatic
