/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Exercise the actual witness without making it part of the public API.
import all MathlibExt.Analysis.ScottishBook151
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis.ScottishBook151Wanted

-- An edge midpoint with opposite signs in the two fixed coordinates.
example : (!₂[1, -1, 0] : EuclideanSpace ℝ (Fin 3)) ∈ CubeEdges ∧
    cubePolynomial !₂[1, -1, 0] = 0 := by
  have hedge : (!₂[1, -1, 0] : EuclideanSpace ℝ (Fin 3)) ∈ CubeEdges := by
    refine ⟨?_, 0, 1, by decide, Or.inl rfl, Or.inr rfl⟩
    intro i
    fin_cases i <;> norm_num [Set.mem_Icc]
  exact ⟨hedge, cubePolynomial_edge _ hedge⟩

-- A point on a face, rather than an edge, where the harmonic witness is nonzero.
example : InnerProductSpace.HarmonicAt cubePolynomial !₂[0, 1 / 2, 1] ∧
    cubePolynomial !₂[0, 1 / 2, 1] = 3 / 16 := by
  refine ⟨cubePolynomial_harmonic _ (Set.mem_univ _), ?_⟩
  norm_num [cubePolynomial]
