/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Bramble
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.Bramble

open _root_.SimpleGraph

-- Non-vacuity: in a connected graph, the whole vertex set forms a bramble of order one.
private theorem univ_isBramble : (pathGraph 3).IsBramble {Set.univ} := by
  refine ⟨?_, ?_⟩
  · intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact (induceUnivIso (pathGraph 3)).connected_iff.mpr (connected_pathGraph_add_one 2)
  · intro X hX Y hY
    rw [Set.mem_singleton_iff] at hX hY
    subst hX hY
    exact Or.inl ⟨0, trivial, trivial⟩

-- It has order greater than zero: the empty set covers nothing.
example : univ_isBramble.OrderGT 0 := by
  intro S hS
  refine ⟨Set.univ, rfl, fun x _ hx => ?_⟩
  simp_all

-- But not order greater than three, the number of vertices.
example : ¬univ_isBramble.OrderGT 3 :=
  IsBramble.not_orderGT_of_card_le _ univ_isBramble (by simp)

end MathlibExtTest.Combinatorics.SimpleGraph.Bramble
