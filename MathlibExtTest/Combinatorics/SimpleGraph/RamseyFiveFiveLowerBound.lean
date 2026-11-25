/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.RamseyFiveFiveLowerBound
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Tests for `MathlibExt.Combinatorics.SimpleGraph.RamseyFiveFiveLowerBound` -/

namespace MathlibExtTest.RamseyFiveFiveLowerBound

open SimpleGraph MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
open MathlibExt.Combinatorics.RamseyErdosLowerBound

-- The bound is not a junk value of `sInf`: the Ramsey property for `(5, 5)` fails on `42`
-- vertices, since otherwise the infimum would be at most `42`.
private theorem not_classicalRamsey_five_five_forty_two : ¬ classicalRamsey 5 5 42 := by
  intro h
  have hle : graphRamsey 5 5 ≤ 42 := by
    rw [graphRamsey_eq_sInf]
    exact Nat.sInf_le h
  have := forty_three_le_graphRamsey_five_five
  omega

-- It fails on every smaller number of vertices too.
example {N : ℕ} (hN : N ≤ 42) : ¬ classicalRamsey 5 5 N := fun h =>
  not_classicalRamsey_five_five_forty_two (classicalRamsey_mono hN h)

-- The docstring's reformulation: some graph on `42` vertices has no `K_5` and no independent set
-- of size `5`.
example : ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ G.IndepSetFree 5 := by
  have h := not_classicalRamsey_five_five_forty_two
  simp only [classicalRamsey, not_forall, not_or] at h
  obtain ⟨G, h1, h2⟩ := h
  refine ⟨G, ?_, ?_⟩
  · by_contra hG
    exact h1 ((not_cliqueFree_iff_top_isContained 5).1 hG)
  · rw [← cliqueFree_compl]
    by_contra hG
    exact h2 ((not_cliqueFree_iff_top_isContained 5).1 hG)

-- The theorem improves the probabilistic bound `11 < R(5, 5)` of the Erdős lower bound tests.
example : 11 < graphRamsey 5 5 := by
  have := forty_three_le_graphRamsey_five_five
  omega

end MathlibExtTest.RamseyFiveFiveLowerBound
