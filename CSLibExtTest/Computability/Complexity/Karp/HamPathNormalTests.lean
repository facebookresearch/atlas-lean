/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathNormal
public meta import CSLibExt.Computability.Complexity.Karp.HamPathNormal

/-! Tests for the backward direction of SAT ≤ HAMPATH on paths with normal detours. -/

namespace Cslib.Complexity.Karp.HamPathNormalTests

open Cslib.Logic.PL

-- One clause, one variable: vertices `0` (clause), `1` (top), `2, …, 5` (row), `6` (bottom).
-- Positive literal: the row runs left to right with the detour `3 → 0 → 4`.
example : CNFSat [[(0, true)]] :=
  cnfSat_of_isHamPath (p := [1, 2, 3, 0, 4, 5, 6])
    (by unfold IsHamPath Cslib.Complexity.Path.arc; decide) (by unfold DetoursNormal; decide)

-- Negative literal: the row runs right to left with the detour `4 → 0 → 3`.
example : CNFSat [[(0, false)]] :=
  cnfSat_of_isHamPath (p := [1, 5, 4, 0, 3, 2, 6])
    (by unfold IsHamPath Cslib.Complexity.Path.arc; decide) (by unfold DetoursNormal; decide)

-- Two clauses, two variables (tops `2, 10, 18`, rows `3, …, 9` and `11, …, 17`): row 0 runs left
-- to right through clause 0, row 1 right to left through clause 1.
example : CNFSat [[(0, true), (1, false)], [(1, false)]] :=
  cnfSat_of_isHamPath (p := [2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 17, 16, 1, 15, 14, 13, 12, 11, 18])
    (by unfold IsHamPath Cslib.Complexity.Path.arc; decide) (by unfold DetoursNormal; decide)

-- With part 1 (`detoursNormal_of_isHamPath`), the Hamiltonian path alone suffices.
example : CNFSat [[(0, true), (1, false)], [(1, false)]] :=
  have h : IsHamPath 19 (hamEdges [[(0, true), (1, false)], [(1, false)]]) 2 18
      [2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 17, 16, 1, 15, 14, 13, 12, 11, 18] := by
    unfold IsHamPath Cslib.Complexity.Path.arc; decide
  cnfSat_of_isHamPath h (detoursNormal_of_isHamPath h)

-- Contracting the detours leaves the diamond chain.
#guard dropClauses [[(0, true)]] [1, 2, 3, 0, 4, 5, 6] = [1, 2, 3, 4, 5, 6]
#guard dropClauses [[(0, true), (1, false)], [(1, false)]]
    [2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 17, 16, 1, 15, 14, 13, 12, 11, 18] =
  [2, 3, 4, 5, 6, 7, 8, 9, 10, 17, 16, 15, 14, 13, 12, 11, 18]
-- Rows read from either end.
#guard (List.range 4).map (hpRo 1 0 true) = [2, 3, 4, 5]
#guard (List.range 4).map (hpRo 1 0 false) = [5, 4, 3, 2]

end Cslib.Complexity.Karp.HamPathNormalTests
