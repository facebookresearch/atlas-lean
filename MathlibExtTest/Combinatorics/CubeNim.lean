/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CubeNim

/-! # Tests for vertex Nim on a cube -/

open MetaMathlibExt

-- The larger piles can lie on either side of each pair. Here they meet at faces 0, 4 and 2.
example : CubeVertexMove ![5, 1, 6, 2, 4, 3] ![2, 1, 3, 2, 1, 3] := by
  exact ⟨0, 4, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩

-- Lowering both faces in a nonempty opposite pair would preserve balance.
example : ¬ CubeVertexMove ![3, 0, 1, 3, 0, 1] ![2, 0, 1, 2, 0, 1] := by
  intro h
  exact cubeVertexNim_pPositions.1 _ _ ⟨rfl, rfl, rfl⟩ h ⟨rfl, rfl, rfl⟩

-- With two tied pairs, a single unequal pair still admits a move to a balanced position.
example : ∃ q, CubeVertexMove ![0, 1, 2, 0, 3, 2] q ∧
    q 0 = q 3 ∧ q 1 = q 4 ∧ q 2 = q 5 := by
  apply cubeVertexNim_pPositions.2
  decide
