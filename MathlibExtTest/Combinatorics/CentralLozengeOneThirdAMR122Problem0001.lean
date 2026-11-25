/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001
import Mathlib.Tactic.NormNum

open MathlibExt.Combinatorics.CentralLozengeOneThirdAMR122Problem0001Wanted

-- At k = 1 the left boundary is an up cell but the corresponding down cell is absent.
example : InHexagon 1 2 1 (-1, 1, false) := by norm_num [InHexagon]
example : ¬InHexagon 1 2 1 (-2, 1, true) := by norm_num [InHexagon]

-- The right boundary has the opposite colors in shifted coordinates.
example : InHexagon 1 2 1 (0, 0, true) := by norm_num [InHexagon]
example : ¬InHexagon 1 2 1 (1, 0, false) := by norm_num [InHexagon]

example :
    (hexagonGraph 1 2 1).Adj ⟨(0, 1, false), by norm_num [InHexagon]⟩
      ⟨(-1, 1, true), by norm_num [InHexagon]⟩ := by
  rw [hexagonGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    exact Bool.false_ne_true (congrArg (fun v ↦ v.val.2.2) h)
  · left
    norm_num [SharesEdge]

-- The theorem specializes to the first nonempty hexagon with the same marked edge.
example :
    3 * Nat.card {M : (hexagonGraph 1 2 1).Subgraph //
        M.IsPerfectMatching ∧ ∀ s t, s.val = (0, 1, false) →
          t.val = (-1, 1, true) → M.Adj s t} =
      Nat.card {M : (hexagonGraph 1 2 1).Subgraph // M.IsPerfectMatching} := by
  simpa using centralLozengeOneThird_holds 1 (by decide)
