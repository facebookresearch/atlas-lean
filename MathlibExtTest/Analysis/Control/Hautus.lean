/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.Hautus

@[expose] public section

open Matrix MathlibExt.Analysis.Control

namespace MathlibExtTest.Analysis.Control.Hautus

/-- The double integrator `ẍ = u`: `A = [[0, 1], [0, 0]]`, `B = [0, 1]ᵀ`. -/
def dblA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Input matrix of the double integrator. -/
def dblB : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- Non-vacuity: the double integrator passes the Hautus test, hence is controllable on
`[0, 1]`. -/
example : IsControllableOn (toEuclideanCLM (𝕜 := ℝ) dblA)
    (toEuclideanLin dblB).toContinuousLinearMap 1 := by
  rw [isControllableOn_iff_hautus _ _ one_pos]
  intro μ w hA hB
  have hB0 := congrFun hB 0
  have hA1 := congrFun hA 1
  simp [dblA, dblB, vecMul, dotProduct, Fin.sum_univ_two] at hB0 hA1
  funext i
  fin_cases i
  · simpa [hB0] using hA1
  · simpa using hB0

/-- A system with zero input matrix fails the Hautus test (take `w = (0, 1)`, `μ = 0`), hence is
not controllable on any `[0, T]` with `T > 0`. -/
example {T : ℝ} (hT : 0 < T) : ¬ IsControllableOn (toEuclideanCLM (𝕜 := ℝ) dblA)
    (toEuclideanLin (0 : Matrix (Fin 2) (Fin 1) ℝ)).toContinuousLinearMap T := by
  rw [isControllableOn_iff_hautus _ _ hT]
  intro h
  have := congrFun (h 0 ![0, 1] (by
    funext j; fin_cases j <;> simp [dblA, vecMul, dotProduct, Fin.sum_univ_two])
    (by simp)) 1
  simp at this

end MathlibExtTest.Analysis.Control.Hautus
