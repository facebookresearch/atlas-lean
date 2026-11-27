/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Convenient.StdSimplexHornRetract

/-!
# Clients of the affine horn retraction

On the edge, the horn at vertex zero contains only that vertex. The test
starts at the opposite vertex and computes the image, then checks that the
homotopy fixes the retracted points in every positive dimension.
-/

open Convexity

example :
    affineHornRetract (0 : Fin 2) (by decide) (StdSimplex.single (R := ℝ) (1 : Fin 2)) =
      StdSimplex.single (R := ℝ) (0 : Fin 2) := by
  let point := affineHornRetract (0 : Fin 2) (by decide) (StdSimplex.single (R := ℝ) (1 : Fin 2))
  obtain ⟨j, hj, hz⟩ := affineHornRetract_horn (0 : Fin 2) (by decide)
    (StdSimplex.single (R := ℝ) (1 : Fin 2))
  have h1 : point.weights 1 = 0 := by
    have h : j = 1 := by fin_cases j <;> simp_all
    simpa [h] using hz
  have h0 := point.total_of_fintype
  rw [Fin.sum_univ_two, h1, add_zero] at h0
  apply StdSimplex.ext
  ext j
  fin_cases j
  · simpa using h0
  · simpa using h1

example {n : ℕ} (k : Fin (n + 1)) (hn : 0 < n)
    (x : StdSimplex ℝ (Fin (n + 1))) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    affineHornHomotopy k hn (affineHornRetract k hn x) s hs = affineHornRetract k hn x :=
  affineHornHomotopy_fix k hn _ (affineHornRetract_horn k hn x) s hs
