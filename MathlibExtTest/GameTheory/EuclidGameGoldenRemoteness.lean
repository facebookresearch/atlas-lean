/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.EuclidGameGoldenRemoteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open SpragueGrundy
open scoped goldenRatio

local instance : DecidableEq euclidGame.Pos := euclidGame.eqDec

private theorem remoteness_root : smithRemoteness euclidGame (1, 1) = 0 :=
  smithRemoteness_of_moves_eq_empty _ _ (by decide)

private theorem remoteness_of_single_move {p q : euclidGame.Pos} (hm : euclidGame.moves p = {q})
    {r : ℕ} (hr : smithRemoteness euclidGame q = r) : smithRemoteness euclidGame p = 1 + r := by
  rw [smithRemoteness_eq, hm, Finset.image_singleton, hr]
  split_ifs with he hv
  · rw [Finset.mem_singleton.mp (Finset.mem_filter.mp (Finset.min'_mem _ he)).1]
  · rw [Finset.max'_singleton]
  · exact (hv (Finset.singleton_nonempty _)).elim

private theorem remoteness_two_one : smithRemoteness euclidGame (2, 1) = 1 :=
  remoteness_of_single_move (by decide) remoteness_root

private theorem remoteness_five_three : smithRemoteness euclidGame (5, 3) = 3 :=
  remoteness_of_single_move (q := (2, 3)) (by decide) <|
    remoteness_of_single_move (q := (2, 1)) (by decide) remoteness_two_one

-- Row three contains (5,3), a next-player win with three forced moves. Check both
-- inequalities directly rather than calling the maximal-remoteness theorem.
example : (5, 3) ∈ calkinWilfRow 3 ∧ euclidPPosition 5 3 = false ∧
    smithRemoteness euclidGame (5, 3) = 3 ∧ φ < (5 : ℝ) / 3 ∧ (5 : ℝ) / 3 < φ + 1 := by
  refine ⟨by decide, by decide, remoteness_five_three, ?_, ?_⟩
  · have h : Real.sqrt 5 < (7 : ℝ) / 3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [Real.goldenRatio]
    linarith
  · linarith [Real.one_lt_goldenRatio]

-- Row two contains (3,1), also a next-player win, but the move skipping two rows
-- reaches the terminal pair and gives remoteness one. Its ratio exceeds the upper bound.
example : (3, 1) ∈ calkinWilfRow 2 ∧ euclidPPosition 3 1 = false ∧
    smithRemoteness euclidGame (3, 1) = 1 ∧ φ + 1 < (3 : ℝ) / 1 := by
  refine ⟨by decide, by decide, ?_, by linarith [Real.goldenRatio_lt_two]⟩
  let root : euclidGame.Pos := (1, 1)
  let parent : euclidGame.Pos := (2, 1)
  have hm : euclidGame.moves (3, 1) = {root, parent} := by decide +revert
  have hroot : smithRemoteness euclidGame root = 0 := remoteness_root
  have hp : smithRemoteness euclidGame parent = 1 := remoteness_two_one
  refine (smithRemoteness_eq euclidGame (3, 1)).trans ?_
  rw [hm, Finset.image_insert, Finset.image_singleton, hroot, hp]
  decide

-- The nearer ratio (3,2) is below the golden ratio and is a P-position instead.
example : euclidPPosition 3 2 = true ∧ (3 : ℝ) / 2 < φ := by
  refine ⟨by decide, ?_⟩
  have h : (2 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [Real.goldenRatio]
  linarith

-- Check the complete move sets in both directions and the rows reached by subtracting twice.
example : euclidGame.moves (7, 2) =
      { (show euclidGame.Pos from (5, 2)), (show euclidGame.Pos from (3, 2)),
        (show euclidGame.Pos from (1, 2)) } ∧
    euclidGame.moves (2, 7) =
      { (show euclidGame.Pos from (2, 5)), (show euclidGame.Pos from (2, 3)),
        (show euclidGame.Pos from (2, 1)) } ∧
    (7, 2) ∈ calkinWilfRow 4 ∧ (2, 7) ∈ calkinWilfRow 4 ∧
    (3, 2) ∈ calkinWilfRow 2 ∧ (2, 3) ∈ calkinWilfRow 2 := by decide

-- Independent terminal checks: a subtraction must leave both piles positive.
example : euclidGame.moves (1, 1) = ∅ ∧ euclidGame.moves (3, 0) = ∅ ∧
    euclidGame.moves (0, 3) = ∅ := by decide

-- Use the public theorem as a client as well as checking the instance independently.
example : φ < (5 : ℝ) / 3 ∧ (5 : ℝ) / 3 < φ + 1 :=
  golden_bounds_of_max_remoteness_N 3 5 3 (by decide) (by decide) (by decide) remoteness_five_three

end MetaMathlibExt
