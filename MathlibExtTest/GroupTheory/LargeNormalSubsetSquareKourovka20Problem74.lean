/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Matrix.Trace
import MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74

/-! Regression tests for Kourovka Notebook Problem 20.74. -/

open MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
open scoped Pointwise

example (G : Type) [Group G] : HasLargeInverseClosedNormalSubsetWithSmallSquare G ↔
    ∃ S : Set G, (∀ g s : G, s ∈ S → g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧
      (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard ∧ S * S ≠ Set.univ :=
  Iff.rfl

example : ¬ ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → HasLargeInverseClosedNormalSubsetWithSmallSquare G →
    Nat.card G ≤ N :=
  finitelyManySimpleGroupsWithLargeNormalSubset_refuted

example : finitelyManyPSL2WithLargeNormalSubset := finitelyManyPSL2WithLargeNormalSubset_holds

local notation "M₅" => Matrix (Fin 2) (Fin 2) (ZMod 5)

-- A trace-zero target: both factors have trace one.
example :
    let A : M₅ := !![2, 1; 2, 4]
    let B : M₅ := !![4, 1; 2, 2]
    let C : M₅ := !![0, -1; 1, 0]
    A.det = 1 ∧ B.det = 1 ∧ A.trace = 1 ∧ B.trace = 1 ∧ C.trace = 0 ∧ A * B = C := by
  dsimp only
  simp only [Matrix.det_fin_two_of, Matrix.trace_fin_two_of, Matrix.mul_fin_two]
  decide

-- A non-scalar trace-two target: the factors have opposite traces.
example :
    let A : M₅ := !![3, 3; 1, 3]
    let B : M₅ := !![2, 1; 3, 2]
    let C : M₅ := !![0, -1; 1, 2]
    A.det = 1 ∧ B.det = 1 ∧ A.trace = 1 ∧ B.trace = -1 ∧ C.trace = 2 ∧ A * B = C := by
  dsimp only
  simp only [Matrix.det_fin_two_of, Matrix.trace_fin_two_of, Matrix.mul_fin_two]
  decide
