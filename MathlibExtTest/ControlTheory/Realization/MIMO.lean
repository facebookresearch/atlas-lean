/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Realization.MIMO
import Mathlib.Tactic.NormNum

open Polynomial Matrix ControlTheory

-- The zero matrix is proper (every entry has `intDegree 0 = 0`), and the
-- theorem applies to it.
example : RatMatrix.IsProper (0 : Matrix (Fin 2) (Fin 2) (RatFunc ℝ)) := by
  intro i j
  simp [RatMatrix.IsProper]

example : ∃ (D : Matrix (Fin 2) (Fin 2) ℝ) (N : Matrix (Fin 2) (Fin 2) ℝ[X])
    (d : ℝ[X]), d.Monic ∧ (∀ i j, (N i j).degree < d.degree) ∧
      ∀ i j, (0 : Matrix (Fin 2) (Fin 2) (RatFunc ℝ)) i j =
        algebraMap ℝ (RatFunc ℝ) (D i j)
          + algebraMap ℝ[X] (RatFunc ℝ) (N i j) / algebraMap ℝ[X] (RatFunc ℝ) d :=
  RatMatrix.exists_commonDenom 0 (by intro i j; simp [RatMatrix.IsProper])

-- A constant matrix is proper, and the theorem applies to it.
example (c : ℝ) :
    ∃ (D : Matrix (Fin 1) (Fin 1) ℝ) (N : Matrix (Fin 1) (Fin 1) ℝ[X])
      (d : ℝ[X]), d.Monic ∧ (∀ i j, (N i j).degree < d.degree) ∧
        ∀ i j, (!![algebraMap ℝ (RatFunc ℝ) c] : Matrix (Fin 1) (Fin 1) (RatFunc ℝ)) i j =
          algebraMap ℝ (RatFunc ℝ) (D i j)
            + algebraMap ℝ[X] (RatFunc ℝ) (N i j) / algebraMap ℝ[X] (RatFunc ℝ) d := by
  apply RatMatrix.exists_commonDenom
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [RatMatrix.IsProper, RatFunc.intDegree_C]

-- An improper entry is rejected: the indeterminate itself has
-- `intDegree 1`, so the 1×1 matrix containing it is not proper.
example : ¬ RatMatrix.IsProper (𝕜 := ℝ)
    (!![RatFunc.X] : Matrix (Fin 1) (Fin 1) (RatFunc ℝ)) := by
  simp [RatMatrix.IsProper, RatFunc.intDegree_X]

-- The strictly proper entry `X⁻¹` (intDegree `-1`) is proper.
example : RatMatrix.IsProper (𝕜 := ℝ)
    (!![(RatFunc.X)⁻¹] : Matrix (Fin 1) (Fin 1) (RatFunc ℝ)) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [RatMatrix.IsProper, RatFunc.intDegree_inv, RatFunc.intDegree_X]

#print axioms RatMatrix.exists_commonDenom
