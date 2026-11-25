/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Logic.Equiv.Fin.Rotate
import MathlibExt.NumberTheory.Digits.PermutipleStrings

open MetaMathlibExt

-- At n = b, the input (3, 1) in base four has the maximal incoming carry.
example {x y : ℕ} (h : IsHoeySloaneStep 4 4 x y (3, 1)) : x = 3 ∧ y = 1 :=
  isHoeySloaneStep_unique 4 4 le_rfl h (by decide)

-- With n > b, one input can label two distinct loops.
example : IsHoeySloaneStep 3 1 0 0 (0, 0) ∧ IsHoeySloaneStep 3 1 1 1 (0, 0) := by
  decide

-- In base four, 312 = 2 × 123. The return path for (2, 3) uses both other inputs.
example : IsMotherGraphEdge 2 4 2 3 ∧
    Relation.ReflTransGen (fun u v : ℕ => (u, v) ∈ [(2, 3), (1, 2), (3, 1)]) 3 2 := by
  have hs : IsPermutipleString 2 4 [(2, 3), (1, 2), (3, 1)] := by
    refine ⟨⟨1, by decide, 1, by decide, 0, by decide, rfl⟩,
      2, ![2, 1, 3], (finRotate 3).symm, ?_, by decide⟩
    unfold IsPermutiple
    decide
  exact isPermutipleString_inputs_isUnion_motherGraphCycles 2 4 (by decide) (by decide)
    hs (2, 3) (by decide)

-- The middle digit of 87912 contributes a loop, whose return path may have length zero.
example : IsMotherGraphEdge 4 10 9 9 ∧
    Relation.ReflTransGen (fun u v : ℕ => (u, v) ∈ [(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)])
      9 9 :=
  isPermutipleString_inputs_isUnion_motherGraphCycles 4 10 (by decide) (by decide)
    isPermutipleString_87912 (9, 9) (by decide)

-- The edge (2, 8) of the graph of 87912 returns from 8 to 2 along the edge (8, 2).
example : IsMotherGraphEdge 4 10 2 8 ∧
    Relation.ReflTransGen (fun u v => ∃ i, ![2, 1, 9, 7, 8] i = u ∧
      ![2, 1, 9, 7, 8] (Fin.revPerm i) = v) 8 2 :=
  permutiple_graph_isUnion_motherGraphCycles 4 10 (by decide) ![2, 1, 9, 7, 8]
    Fin.revPerm isPermutiple_87912 0

-- The middle digit of 87912 contributes a loop, whose return path has length zero.
example : IsMotherGraphEdge 4 10 9 9 ∧
    Relation.ReflTransGen (fun u v => ∃ i, ![2, 1, 9, 7, 8] i = u ∧
      ![2, 1, 9, 7, 8] (Fin.revPerm i) = v) 9 9 :=
  permutiple_graph_isUnion_motherGraphCycles 4 10 (by decide) ![2, 1, 9, 7, 8]
    Fin.revPerm isPermutiple_87912 2

-- In base one every digit is zero, so the only graph edge is the loop at zero.
example : IsMotherGraphEdge 1 1 0 0 ∧
    Relation.ReflTransGen (fun u v => ∃ i : Fin 1, (fun _ => 0) i = u ∧
      (fun _ => 0) ((1 : Equiv.Perm (Fin 1)) i) = v) 0 0 := by
  have hp : IsPermutiple 1 1 (fun _ : Fin 1 => 0) 1 :=
    ⟨fun _ => Nat.zero_lt_one, by decide⟩
  exact permutiple_graph_isUnion_motherGraphCycles 1 1 (by decide) (fun _ => 0) 1 hp 0

-- The maximal incoming carry cancels a negative digit difference, leaving zero outgoing carry.
example : IsHoeySloaneStep 4 5 3 0 (3, 0) :=
  isHoeySloaneStep_hoeySloaneTransition 4 5 (by decide) (by decide) (3, 0) (by decide)

-- In the same machine the largest second digit can take zero to the maximal outgoing carry.
example : IsHoeySloaneStep 4 5 0 3 (1, 4) :=
  isHoeySloaneStep_hoeySloaneTransition 4 5 (by decide) (by decide) (1, 4) (by decide)
