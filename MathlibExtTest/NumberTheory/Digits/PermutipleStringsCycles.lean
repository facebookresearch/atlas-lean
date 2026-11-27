/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Rotate
import MathlibExt.NumberTheory.Digits.PermutipleStringsCycles

open MetaMathlibExt

-- The rotation in 102564 = 4 * 025641 has a six-digit cycle, so the return
-- path from 1 to 4 is not just the reverse of an edge.
example :
    let d : Fin 6 → ℕ := ![4, 6, 5, 2, 0, 1]
    let σ := (finRotate 6).symm
    IsMotherGraphEdge 4 10 4 1 ∧
      Relation.ReflTransGen (fun u v => ∃ i, d i = u ∧ d (σ i) = v) 1 4 := by
  dsimp only
  have hp : IsPermutiple 4 10 (k := 5) ![4, 6, 5, 2, 0, 1] (finRotate 6).symm := by
    unfold IsPermutiple
    decide
  exact permutiple_graph_isUnion_motherGraphCycles 4 10 (by decide) _ _ hp 0

-- A zero-digit loop with multiplier greater than the base needs no return step.
example : IsMotherGraphEdge 3 1 0 0 ∧
    Relation.ReflTransGen (fun u v => ∃ _ : Fin 1, 0 = u ∧ 0 = v) 0 0 :=
  permutiple_graph_isUnion_motherGraphCycles 3 1 (by decide) (k := 0) (fun _ ↦ 0)
    (Equiv.refl _) (by unfold IsPermutiple; decide) 0
