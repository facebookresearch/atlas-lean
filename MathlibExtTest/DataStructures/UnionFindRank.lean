/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.UnionFindRank
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-- Boundary check: on a two-node chain `0 -> 1` (root `1`), the
find depth of `0` is at most the root's rank, with ranks `0, 5`. -/
example : (1 : ℕ) ≤ ![0, 5] ((fun i : Fin 2 => ![1, 1] i)^[1] (0 : Fin 2)) :=
  find_depth_le_rank (p := fun i : Fin 2 => ![1, 1] i) (r := ![0, 5])
    (by decide) 0 1 (by decide) (by decide)
