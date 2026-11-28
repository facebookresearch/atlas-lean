/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on chordal bipartite graphs is NP-complete

Source:
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53(2-3) (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DominatingSetChordalBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on chordal bipartite graphs is NP-complete

INSTANCE: a chordal bipartite graph `G = (V, E)` (a bipartite graph in which every cycle of
length at least `6` has a chord) and a positive integer `K`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K`, that is, every vertex not in `V'`
has a neighbor in `V'`?

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds that the graph is chordal bipartite:
bipartite, as Mathlib's `SimpleGraph.IsBipartite` (`Colorable 2`), and without a chordless cycle of length at
least `6`, that is, no cycle graph `Cₖ` with `k ≥ 6` is an induced subgraph (Mathlib's
`SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`; a cycle has a chord exactly when its
vertices do not induce a cycle graph). As in the source, `K` is positive.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DOMINATING SET on chordal bipartite graphs is NP-complete.** Source: Müller and
Brandstädt (1987). -/
public theorem_wanted dominatingSetChordalBipartite_npComplete :
    dominatingSetChordalBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetChordalBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalBipartite
