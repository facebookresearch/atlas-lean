/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Online.CompetitiveFramework
import CSLibExt.Algorithms.Lean.Online.ListUpdate
import CSLibExt.Algorithms.Lean.Online.ListUpdateCompetitive
import Mathlib.Tactic

open Cslib.Algorithms.Lean.Online.CompetitiveFramework
open Cslib.Algorithms.Lean.Online.ListUpdate

example : run (mtfStrategy ([1, 2, 3] : List ℕ)) [3, 1]
    = [(3, [3, 1, 2]), (1, [1, 3, 2])] := rfl

example : algCost (listUpdateProblem ([1, 2, 3] : List ℕ))
    (mtfStrategy [1, 2, 3]) [3, 1] = ((5 : ℕ) : ℝ) :=
  algCost_mtfStrategy _ _ (by decide)

example : StrictCompetitive (listUpdateProblem ([1, 2, 3] : List ℕ))
    (mtfStrategy [1, 2, 3]) 2 :=
  mtf_strictCompetitive (by decide)

example : ∃ σ : List ℕ, (listUpdateProblem ([1, 2, 3] : List ℕ)).legal σ ∧
    ENNReal.ofReal 1 * optCost (listUpdateProblem [1, 2, 3]) σ +
      ENNReal.ofReal 0 < ENNReal.ofReal
      (algCost (listUpdateProblem [1, 2, 3]) (mtfStrategy [1, 2, 3]) σ) :=
  listUpdate_additiveLowerBound (by decide) (by decide) (mtfStrategy [1, 2, 3])
    (mtfStrategy_feasible [1, 2, 3]) 1 0 (by norm_num)
    (by norm_num [show ([1, 2, 3].length) = 3 from rfl]) le_rfl

example : stepCost [1, 2, 3] 1 [1, 3, 2] = 2 := by
  decide

example : traceCost [1, 2, 3] [(1, [1, 3, 2])] = 2 := by
  decide

example : traceCost [1, 2, 3] [(1, [1, 3, 2]), (2, [2, 1, 3])] = 5 := by
  decide
