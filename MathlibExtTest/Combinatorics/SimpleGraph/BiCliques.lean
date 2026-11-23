/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.BiCliques

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.BiCliques

open MetaMathlibExt

-- Combinatorics 480: Contains a (c,d)-Biclique

lemma SimpleGraph.ContainsBiclique.one_one_of_adj {V : Type*} [Fintype V]
   (G : SimpleGraph V) (u v : V) (h : G.Adj u v) :
    G.ContainsBiclique 1 1 := by
  refine ⟨{u}, {v}, by simp, by simp, ?_, ?_⟩
  · rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact G.ne_of_adj h
  · intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact h

-- Combinatorics 493: Biclique Number

lemma SimpleGraph.bicliqueNumber_nonneg {V : Type*} [Fintype V]
    (G : SimpleGraph V) : 0 ≤ G.bicliqueNumber :=
  Nat.zero_le _

end MathlibExtTest.Combinatorics.SimpleGraph.BiCliques

end
