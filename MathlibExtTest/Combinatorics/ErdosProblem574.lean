/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
import MathlibExt.Combinatorics.ErdosProblem574

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem574Wanted

/-- Erdős Problem 574 is false. -/
example : ¬ conjecture := conjecture_refuted

/-- The blow-up of the Wenger graph over `ZMod 2` has 24 vertices. -/
example : Fintype.card
    ((ZMod 2 × ZMod 2 × ZMod 2) ⊕ ((ZMod 2 × ZMod 2 × ZMod 2) × Fin 2)) = 24 := by
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]

/-- The blow-up of the Wenger graph over `ZMod 2` has 32 edges. -/
example : (Wenger.blowGraph (K := ZMod 2)).edgeSet.ncard = 32 := by
  rw [Wenger.blowGraph_edgeSet_ncard, ZMod.card]
  norm_num

/-- The blow-up of the Wenger graph over `ZMod 2` has no 5-cycle. -/
example : (SimpleGraph.cycleGraph 5).Free (Wenger.blowGraph (K := ZMod 2)) :=
  Wenger.blowGraph_free_five

/-- The blow-up of the Wenger graph over `ZMod 2` has no 6-cycle. -/
example : (SimpleGraph.cycleGraph 6).Free (Wenger.blowGraph (K := ZMod 2)) :=
  Wenger.blowGraph_free_six

/-- An adjacent pair in the Wenger graph over `ZMod 2`. -/
example : Wenger.adj ((0, 0, 0) : ZMod 2 × ZMod 2 × ZMod 2) (0, 0, 0) := ⟨by decide, by decide⟩

/-- A nonadjacent pair in the Wenger graph over `ZMod 2`. -/
example : ¬ Wenger.adj ((1, 0, 0) : ZMod 2 × ZMod 2 × ZMod 2) (0, 1, 0) :=
  fun h => absurd h.1 (by decide)

/-- The lower bound at $m = 0$: 32 edges on 24 vertices. -/
example : 32 ≤ extremalNumber 3 24 := extremalNumber_three_lower 0

end MathlibExt.Combinatorics.ErdosProblem574Wanted
