/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-DECOMPOSITION is NP-complete for every fixed H with a component of at least 3 edges

Source:
D. Dor and M. Tarsi, "Graph decomposition is NP-complete: a complete proof of Holyer's
conjecture", SIAM Journal on Computing 26 (1997), 1166-1187, doi:10.1137/S0097539792229507.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HDecompositionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HDecomposition

/-!
# H-DECOMPOSITION is NP-complete for every fixed H with a component of at least 3 edges

For a fixed graph `H`: INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have an
`H`-decomposition, that is, a partition of `E` into subgraphs isomorphic to `H`? Dor and Tarsi
prove this NP-complete whenever `H` has a connected component with at least three edges
(Holyer's conjecture).

`H` is not part of the instance: it is the pattern `(m, hs)` (vertices `Fin m`, simple edge list
`hs`), a parameter of the decision problem `hDecompositionDec m hs`, and the theorem is stated
for every pattern satisfying `ValidPattern`: `hs` is a simple edge list and some connected
component of `H` (Mathlib's `SimpleGraph.ConnectedComponent.toSimpleGraph`, the subgraph of `H`
induced on the component) has at least three edges.

A subgraph of `G` isomorphic to `H` is the image of a Mathlib `SimpleGraph.Copy` of `H` in `G`
(an injective map of vertices sending edges to edges); its edge set is the image of `H`'s edge
set under `Sym2.map`. An `H`-decomposition is a finite family of copies whose edge sets
partition `E`: every edge of `G` lies in the edge set of exactly one copy.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **H-DECOMPOSITION is NP-complete for every fixed `H` with a connected component of at least
three edges.** Source: Dor and Tarsi (1997). -/
public theorem_wanted hDecomposition_npComplete (m : ℕ) (hs : List (ℕ × ℕ))
    (hH : ValidPattern m hs) :
    hDecompositionDec m hs ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (hDecompositionDec m hs)

end MetaMathlibExt.Complexity.NPComplete.HDecomposition
