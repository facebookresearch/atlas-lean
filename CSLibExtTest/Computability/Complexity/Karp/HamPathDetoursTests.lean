/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathDetours

/-! Tests for the normal-detour theorem of Sipser's SAT-to-HAMPATH construction. -/

namespace Cslib.Complexity.Karp.HamPathDetoursTests

open Cslib.CookLevin Cslib.Logic.PL

-- `[[(0, true)]]`: clause `0`, top `1`, row `2, 3, 4, 5`, bottom `6`. The path goes left to right
-- and detours from `3` through clause `0` to `4`; the theorem's hypothesis is inhabited.
example : DetoursNormal [[(0, true)]] [1, 2, 3, 0, 4, 5, 6] :=
  detoursNormal_of_isHamPath (by unfold IsHamPath Path.arc; decide)

-- `[[(0, true), (0, false)]]` has both detours; a right-to-left path uses the negative one.
example : DetoursNormal [[(0, true), (0, false)]] [1, 5, 4, 0, 3, 2, 6] :=
  detoursNormal_of_isHamPath (by unfold IsHamPath Path.arc; decide)

-- The predicate is not vacuous: a clause entered from one pair and left to the separator.
example : ¬ DetoursNormal [[(0, true)]] [1, 2, 3, 0, 5, 4, 6] := by
  unfold DetoursNormal; decide

-- The arcs into the clause vertex of `[[(0, true)]]` come from its pair (here only `3`).
example : (hamEdges [[(0, true)]]).filter (·.2 = 0) = [(3, 0)] := by decide

end Cslib.Complexity.Karp.HamPathDetoursTests
