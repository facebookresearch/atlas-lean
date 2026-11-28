/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on triangle-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET;
S. Poljak, "A note on stable sets and colorings of graphs", Commentationes
Mathematicae Universitatis Carolinae 15 (1974), 307-309.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleFreeIndependentSet

/-!
# INDEPENDENT SET on triangle-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that contains no triangle, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

Poljak's construction gives the reduction from INDEPENDENT SET: replacing every edge of a graph
with `m` edges by a path of three edges yields a triangle-free graph whose independence number
is larger by exactly `m`. INDEPENDENT SET itself is proved NP-complete in
`CSLibExt.Computability.Complexity.Karp` (`Cslib.Complexity.Karp.indSetDec`, with its own
adjacency-bit encoding); this module states the restriction to triangle-free graphs with the
edge-list encoding of the statements in this directory.

"No triangle" is Mathlib's `SimpleGraph.CliqueFree 3`; the independent set is a `Finset` whose
coercion is `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET is NP-complete on triangle-free graphs.** Source: Garey and Johnson
(1979), [GT20]; Poljak (1974). -/
public theorem_wanted triangleFreeIndependentSet_npComplete :
    triangleFreeIndependentSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangleFreeIndependentSetDec

end MetaMathlibExt.Complexity.NPComplete.TriangleFreeIndependentSet
