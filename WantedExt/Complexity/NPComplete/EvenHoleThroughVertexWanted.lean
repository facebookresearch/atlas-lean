/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVEN HOLE THROUGH A GIVEN VERTEX is NP-complete

Source:
D. Bienstock, "On the complexity of testing for odd holes and induced odd paths", Discrete
Mathematics 90 (1991), 85-92, doi:10.1016/0012-365X(91)90098-M, and "Corrigendum", Discrete
Mathematics 102 (1992), 109, doi:10.1016/0012-365X(92)90357-L;
H.-T. Cheong and H.-I. Lu, "Finding a shortest even hole in polynomial time", Journal of Graph
Theory 99 (2022), 425-434, doi:10.1002/jgt.22748 (arXiv:2008.06740; abstract: "Bienstock
[DM 1991 and 1992] proved that detecting an even (respectively, odd) hole containing a given
vertex is NP-complete").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EvenHoleThroughVertexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex

/-!
# EVEN HOLE THROUGH A GIVEN VERTEX is NP-complete

INSTANCE: a graph `G = (V, E)` and a vertex `v ∈ V`. QUESTION: does `G` have an even hole
containing `v`, i.e., an induced cycle of even length at least `4` through `v`?

Cheong and Lu (2022): "An even (respectively, odd) hole in a graph is an induced cycle with even
(respectively, odd) length that is at least four. Bienstock [DM 1991 and 1992] proved that
detecting an even (respectively, odd) hole containing a given vertex is NP-complete." Testing for
an even hole anywhere in the graph is polynomial (Conforti, Cornuéjols, Kapoor and Vušković).

The instance, its graph and its well-formedness are those of
`OddHoleThroughVertex`: the vertex count `n` (vertices `Fin n`), a simple edge list and the given
vertex `v < n`. As there, a hole of length `k` is an induced copy of Mathlib's
`SimpleGraph.cycleGraph k`, a graph embedding `cycleGraph k ↪g G` (injective, preserving and
reflecting adjacency, so chordless); it is even when `k` is even, and contains `v` when `v` is
the image of one of its vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EVEN HOLE THROUGH A GIVEN VERTEX is NP-complete.** Source: Bienstock (1991, 1992); Cheong
and Lu (2022). -/
public theorem_wanted evenHoleThroughVertex_npComplete :
    evenHoleThroughVertexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L evenHoleThroughVertexDec

end MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex
