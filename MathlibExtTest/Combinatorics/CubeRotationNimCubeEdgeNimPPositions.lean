/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CubeRotationNimCubeEdgeNimPPositions

/-!
# Tests for P-positions of edge Nim on a cube

Concrete positions illustrate the obstruction to moves between equal pair Nim-sums and
the existence of moves to equal pair Nim-sums.

Source: Balaji R. Kadam and A. J. Shaiju, *Variations of the Nim Game Played on a Cube*,
INTEGERS 25 (2025), Article G2, Theorem 3.
-/

namespace MathlibExtTest.Combinatorics.CubeRotationNimCubeEdgeNimPPositions

open MetaMathlibExt

example (q : Fin 6 → ℕ) (h : CubeEdgeMove ![1, 1, 1, 0, 0, 0] q) :
    ¬ (q 0 ^^^ q 3 = q 1 ^^^ q 4 ∧ q 1 ^^^ q 4 = q 2 ^^^ q 5) := by
  exact cubeEdgeNim_pPositions.1 _ _ (by decide) h

example : ¬ CubeEdgeMove ![3, 0, 1, 3, 0, 1] ![2, 0, 1, 2, 0, 1] := by
  intro h
  exact cubeEdgeNim_pPositions.1 _ _ (by decide) h (by decide)

example : ∃ q, CubeEdgeMove ![5, 1, 2, 2, 4, 3] q ∧
    q 0 ^^^ q 3 = q 1 ^^^ q 4 ∧ q 1 ^^^ q 4 = q 2 ^^^ q 5 := by
  apply cubeEdgeNim_pPositions.2
  decide

end MathlibExtTest.Combinatorics.CubeRotationNimCubeEdgeNimPPositions
