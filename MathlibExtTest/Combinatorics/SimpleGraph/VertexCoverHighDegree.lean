/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexCoverHighDegree
import Mathlib.Combinatorics.SimpleGraph.Star

@[expose] public section

open SimpleGraph

/-- The center of the star on `Fin 4` has degree `3`, so it belongs to every vertex cover with
at most two vertices. -/
example (C : Finset (Fin 4)) (hC : (starGraph (0 : Fin 4)).IsVertexCover ↑C)
    (hk : C.card ≤ 2) : (0 : Fin 4) ∈ C :=
  mem_of_card_le_of_lt_degree _ C hC hk (by decide)

/-- The bound is sharp: the three leaves form a vertex cover of size `3` that omits the
center. -/
example : (starGraph (0 : Fin 4)).IsVertexCover ↑({1, 2, 3} : Finset (Fin 4)) ∧
    ({1, 2, 3} : Finset (Fin 4)).card = 3 ∧ (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4)) := by
  refine ⟨?_, by decide, by decide⟩
  unfold IsVertexCover
  decide

end
