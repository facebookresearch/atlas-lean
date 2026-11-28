/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import MathlibExt.Combinatorics.SimpleGraph.RamseyThreeFive
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-! # Boundary tests for the Ramsey property for a triangle and an independent five-set -/

namespace MathlibExtTest.RamseyThreeFive

open SimpleGraph MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
open MathlibExt.Combinatorics.RamseyErdosLowerBound

-- A triangle-free graph on fourteen vertices must have an independent five-set.
example (G : SimpleGraph (Fin 14)) (ht : G.CliqueFree 3) :
    ∃ s, G.IsNIndepSet 5 s := by
  have h : classicalRamsey 3 5 (graphRamsey 3 5) :=
    Nat.sInf_mem (s := {n | classicalRamsey 3 5 n}) (exists_classicalRamsey 3 5)
  rw [graphRamsey_three_five] at h
  have hc := (h G).resolve_left (fun hc => hc.not_cliqueFree ht)
  simpa [CliqueFree] using hc.not_cliqueFree

-- On thirteen vertices both configurations can be avoided simultaneously.
example : ∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ G.IndepSetFree 5 := by
  have h : ¬ classicalRamsey 3 5 13 := by
    intro h
    have hle : graphRamsey 3 5 ≤ 13 := Nat.sInf_le h
    rw [graphRamsey_three_five] at hle
    omega
  simpa [classicalRamsey, ← not_cliqueFree_iff_top_isContained] using h

end MathlibExtTest.RamseyThreeFive

namespace MathlibExtTest.RamseyThreeThree

open SimpleGraph

example : graphRamsey 3 3 = 6 := graphRamsey_three_three

-- The five-cycle and its complement both have zero triangles, checked independently of R(3,3).
example : (cycleGraph 5).cliqueFinset 3 = ∅ ∧ (cycleGraph 5)ᶜ.cliqueFinset 3 = ∅ := by
  constructor <;> decide +kernel

-- On six vertices, the cycle is triangle-free, but the even vertices form a triangle
-- in the complement. Swapping the graph and its complement gives the other branch.
example : (cycleGraph 6).CliqueFree 3 ∧
    (cycleGraph 6)ᶜ.IsNClique 3 ({0, 2, 4} : Finset (Fin 6)) := by
  exact ⟨cliqueFinset_eq_empty_iff.mp (by decide +kernel), by decide +kernel⟩

end MathlibExtTest.RamseyThreeThree
