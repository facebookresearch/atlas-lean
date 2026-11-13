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

/-- **Robertson–Seymour theorem.** Let $F$ be a family of finite simple graphs that is closed
under taking minors: whenever $G \in F$ and $H$ is a minor of $G$, also $H \in F$. Then any two
finite graphs that are minors of each other are isomorphic, and there is a finite set $O$ of
finite graphs such that a finite graph $G$ belongs to $F$ if and only if no graph in $O$ is a
minor of $G$.

Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
theorem_wanted robertson_seymour
    (F : Set FinGraph)
    (h_closed : ∀ G H, IsMinor H G → G ∈ F → H ∈ F) :
    (∀ G H : FinGraph, IsMinor G H → IsMinor H G →
      Nonempty (G.G ≃g H.G)) ∧
    ∃ (Obstructions : Set FinGraph) (_ : Obstructions.Finite),
      ∀ G, G ∈ F ↔ ∀ H ∈ Obstructions, ¬IsMinor H G

end MetaMathlibExt
