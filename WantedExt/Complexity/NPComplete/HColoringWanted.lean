/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-COLORING is NP-complete for every fixed non-bipartite H

Source:
P. Hell and J. Nešetřil, "On the complexity of H-coloring", Journal of Combinatorial Theory,
Series B 48 (1990), 92-110, doi:10.1016/0095-8956(90)90132-J.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HColoring

/-!
# H-COLORING is NP-complete for every fixed non-bipartite H

For a fixed simple graph `H`: INSTANCE: a graph `G = (V, E)`. QUESTION: is there an
`H`-coloring of `G`, that is, a homomorphism `G → H` (a map `V(G) → V(H)` sending every edge of
`G` to an edge of `H`)? Hell and Nešetřil prove this NP-complete whenever `H` is not bipartite
(when `H` is bipartite it is solvable in polynomial time).

`H` is not part of the instance: it is the pattern `(m, hs)` (vertices `Fin m`, simple edge list
`hs`), a parameter of the decision problem `hColoringDec m hs`, and the theorem is stated for
every pattern satisfying `ValidPattern`: `hs` is a simple edge list and `H` is not bipartite
(Mathlib's `SimpleGraph.IsBipartite`, that is, not 2-colorable). The question and the
well-formedness condition are those of `WantedExt.Complexity.NPComplete.GraphHomomorphismWanted`
applied to the instance with that fixed target (`withPattern`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **H-COLORING is NP-complete for every fixed non-bipartite `H`.** Source: Hell and Nešetřil
(1990). -/
public theorem_wanted hColoring_npComplete (m : ℕ) (hs : List (ℕ × ℕ))
    (hH : ValidPattern m hs) :
    hColoringDec m hs ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hColoringDec m hs)

end MetaMathlibExt.Complexity.NPComplete.HColoring
