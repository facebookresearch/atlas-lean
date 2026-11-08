/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.EdgeTranspositionGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.EdgeTranspositionGraph

open MetaMathlibExt

-- Combinatorics 432: Edge-transposition graph

-- Sanity check: the transposition graph for (02) in S_3 (on 0,1,2) has 1 edge and the vertex 1 is isolated

abbrev swap : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- Decidability of the relation defining the `(02)` transposition graph. -/

instance : DecidableRel
    (fun i j : Fin 3 => Equiv.swap i j ∈ ({swap} : Set (Equiv.Perm (Fin 3)))) :=
  fun i j => decidable_of_iff _ Set.mem_singleton_iff

/-- Decidability of adjacency in the `(02)` transposition graph: unfold to
    `fromRel` so Mathlib's decidability instance fires. -/

instance : DecidableRel (edgeTranspositionGraph {swap}).Adj := by
  unfold edgeTranspositionGraph
  infer_instance

example :
    let TG := edgeTranspositionGraph {swap}
    TG.edgeFinset.card = 1 ∧ TG.degree 1 = 0 := by
  decide

end MathlibExtTest.Combinatorics.SimpleGraph.EdgeTranspositionGraph

end
