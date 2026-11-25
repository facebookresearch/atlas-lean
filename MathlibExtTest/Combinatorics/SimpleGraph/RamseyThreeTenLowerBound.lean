/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Clique
import MathlibExt.Combinatorics.SimpleGraph.RamseyThreeTenLowerBound

/-! # A boundary test for the lower bound on `R(3, 10)` -/

namespace MathlibExtTest.RamseyThreeTenLowerBound

open SimpleGraph
open MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted (forty_le_graphRamsey_three_ten)

-- At 39 vertices a graph can avoid a triangle and an independent ten-set simultaneously.
example : ∃ G : SimpleGraph (Fin 39), G.CliqueFree 3 ∧ G.IndepSetFree 10 := by
  have h : ¬ classicalRamsey 3 10 39 := by
    intro hRamsey
    have hle : graphRamsey 3 10 ≤ 39 := Nat.sInf_le hRamsey
    exact (by decide : ¬ 40 ≤ 39) (forty_le_graphRamsey_three_ten.trans hle)
  classical
  simpa [classicalRamsey, ← not_cliqueFree_iff_top_isContained] using h

end MathlibExtTest.RamseyThreeTenLowerBound
