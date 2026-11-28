/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE-WIDTH is NP-complete

Source:
M. R. Fellows, F. A. Rosamond, U. Rotics and S. Szeider, "Clique-width is NP-complete",
SIAM Journal on Discrete Mathematics 23(2) (2009), 909-939, doi:10.1137/070687256;
definition of `k`-expressions and clique-width: B. Courcelle and S. Olariu, "Upper bounds to the
clique width of graphs", Discrete Applied Mathematics 101(1-3) (2000), 77-114,
doi:10.1016/S0166-218X(99)00184-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CliqueWidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueWidth

/-!
# CLIQUE-WIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected, with at least one vertex) and an
integer `K`. QUESTION: is the clique-width of `G` at most `K`? Fellows, Rosamond, Rotics and Szeider (2009): "given a graph
`G` and an integer `k`, deciding whether the clique-width of `G` is at most `k` is NP-complete."

The clique-width of `G` (Courcelle and Olariu, 2000) is the least `k` such that `G` is the
graph of a `k`-expression: a term built from `k` vertex labels by the operations
- `i(v)`: create a single vertex `v` with label `i`;
- `G ⊕ H`: disjoint union of two labelled graphs;
- `η_{i,j}` with `i ≠ j`: add an edge between every vertex labelled `i` and every vertex
  labelled `j`;
- `ρ_{i→j}`: relabel every vertex with label `i` to label `j`.

`Generated k V H l` says that the graph `H` on the vertex type `V` with labelling
`l : V → Fin k` is the value of some `k`-expression; its four constructors are the four
operations (disjoint union is Mathlib's `SimpleGraph.sum`, `⊕g`, on `V ⊕ W`). The labels are
`Fin k`, so `k` labels. The clique-width of `G` is at most `K` when `G` is isomorphic (`≃g`) to
the graph of some `K`-expression, under any final labelling. Every `k`-expression creates at
least one vertex, so clique-width is defined only for graphs with a vertex, and `WellFormed`
requires `0 < n`. With `K = 0` no vertex can be created, so `K = 0` is a no-instance.

The graph is given by an edge list on `Fin n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLIQUE-WIDTH is NP-complete.** Source: Fellows, Rosamond, Rotics and Szeider (2009). -/
public theorem_wanted cliqueWidth_npComplete :
    cliqueWidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueWidthDec

end MetaMathlibExt.Complexity.NPComplete.CliqueWidth
