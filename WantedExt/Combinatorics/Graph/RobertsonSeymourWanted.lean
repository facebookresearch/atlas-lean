/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.GraphMinor
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

/-- **Robertson–Seymour theorem, forbidden-minor form.** Every family `F` of finite simple graphs
that is closed under taking minors (`MetaMathlibExt.IsMinor`) is characterised by a finite set of
forbidden minors: there is a finite set `Obstructions` of finite graphs such that `G ∈ F` if and
only if no member of `Obstructions` is a minor of `G` (Diestel, *Graph Theory*, 6th ed., author's
online preview of Chapter 12, Corollary 12.7.2, "the Kuratowski set for any minor-closed graph
property is finite", a consequence of the graph minor theorem, Theorem 12.7.1,
`MetaMathlibExt.graph_minor_theorem`). The statement also records that graphs which are minors
of each other are isomorphic; that conjunct is elementary (every minor step other than an
isomorphism strictly decreases the number of vertices plus edges, so graphs that are minors of
each other are linked by isomorphism steps only) and is not part of the theorem of Robertson and
Seymour.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
theorem_wanted robertson_seymour
    (F : Set FinGraph)
    (h_closed : ∀ G H, IsMinor H G → G ∈ F → H ∈ F) :
    (∀ G H : FinGraph, IsMinor G H → IsMinor H G →
      Nonempty (G.G ≃g H.G)) ∧
    ∃ (Obstructions : Set FinGraph) (_ : Obstructions.Finite),
      ∀ G, G ∈ F ↔ ∀ H ∈ Obstructions, ¬IsMinor H G

/-- **Graph minor theorem (Robertson–Seymour).** The finite graphs are well-quasi-ordered by the
minor relation: every infinite sequence of finite graphs has two terms `G i, G j` with `i < j`
such that `G i` is a minor of `G j` (Diestel, *Graph Theory*, 6th ed., Theorem 12.7.1; its
Corollary 12.7.2 is the forbidden-minor form `MetaMathlibExt.robertson_seymour`). -/
theorem_wanted graph_minor_theorem (G : ℕ → FinGraph.{0}) : ∃ i j, i < j ∧ IsMinor (G i) (G j)

end MetaMathlibExt
