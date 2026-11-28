/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ConsistentlyOrdered
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open MetaMathlibExt.Matrix

-- Two consecutive diagonal blocks, with nonzero diagonal entries and nonsymmetric off-diagonal
-- blocks. In particular, the off-diagonal edge from 0 to 3 need not have consecutive indices.
private def twoBlockMatrix : Matrix (Fin 4) (Fin 4) ℕ :=
  Matrix.of ![![1, 0, 0, 0], ![0, 2, 1, 0], ![1, 0, 3, 0], ![1, 1, 0, 4]]

private theorem twoBlockMatrix_isConsistentlyOrdered : IsConsistentlyOrdered twoBlockMatrix := by
  let block : Fin 4 → Fin 2 := ![0, 0, 1, 1]
  refine IsConsistentlyOrdered.of_block_tridiagonal block (by decide +revert) ?_
  intro i j
  dsimp only [block]
  fin_cases i <;> fin_cases j <;> decide

example : (SimpleGraph.fromRel (fun i j ↦ twoBlockMatrix i j ≠ 0)).Colorable 2 :=
  twoBlockMatrix_isConsistentlyOrdered.colorable_support

-- Ordinary tridiagonal matrices use singleton blocks.
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hzero : ∀ ⦃i j : Fin n⦄, i ≠ j → (i : ℕ) + 1 ≠ (j : ℕ) →
      (j : ℕ) + 1 ≠ (i : ℕ) → A i j = 0) :
    IsConsistentlyOrdered A :=
  IsConsistentlyOrdered.of_block_tridiagonal id monotone_id hzero

-- The same undirected cycle in path order: 0–1–2–3, with the closing edge 0–3. Each edge is
-- present in exactly one triangle of the matrix, and neither triangle alone gives the obstruction.
private def orderedCycle : Matrix (Fin 4) (Fin 4) ℕ :=
  Matrix.of ![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 1], ![1, 0, 0, 0]]

example : (SimpleGraph.fromRel (fun i j ↦ orderedCycle i j ≠ 0)).Colorable 2 := by
  let color : Fin 4 → Fin 2 := ![0, 1, 0, 1]
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro i j
  change (i ≠ j ∧ (orderedCycle i j ≠ 0 ∨ orderedCycle j i ≠ 0)) → color i ≠ color j
  dsimp only [color]
  fin_cases i <;> fin_cases j <;> decide

example : ¬ IsConsistentlyOrdered orderedCycle := by
  rintro ⟨layer, step⟩
  have h01 : layer 1 = layer 0 + 1 := step (by decide) (Or.inl (by decide))
  have h12 : layer 2 = layer 1 + 1 := step (by decide) (Or.inr (by decide))
  have h23 : layer 3 = layer 2 + 1 := step (by decide) (Or.inl (by decide))
  have h03 : layer 3 = layer 0 + 1 := step (by decide) (Or.inr (by decide))
  omega

example (A : Matrix (Fin 0) (Fin 0) ℕ) : IsConsistentlyOrdered A := by
  refine ⟨fun i ↦ i.elim0, ?_⟩
  intro i
  exact i.elim0
