/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED DIAMETER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED
DIAMETER;
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (NP-complete already for `K = 2`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OrientedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedDiameter

/-!
# ORIENTED DIAMETER is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can the edges of `G`
be oriented so that the resulting directed graph is strongly connected and has diameter no more
than `K`?

An orientation is a Mathlib `Digraph` `D` on `V` whose arcs choose exactly one direction for each
edge: `(Graph i).IsOrientation D.Adj`, the existing MathlibExt predicate
`SimpleGraph.IsOrientation` (every arc is an edge of `G`, and every edge `{u, v}` carries exactly
one of `u → v`, `v → u`). The diameter of `D` is at most `K` when every vertex `v` can
be reached from every vertex `u` along at most `K` arcs (`ReachWithin`: a sequence of `K + 1`
vertices from `u` to `v` in which each step stays put or follows an arc). Diameter at most `K`
means every ordered pair is joined by a directed path, so it implies strong connectivity; the
question's first condition is therefore not repeated as a separate conjunct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ORIENTED DIAMETER is NP-complete.** Source: Garey and Johnson (1979), [GT64]; Chvátal and
Thomassen (1978). -/
public theorem_wanted orientedDiameter_npComplete :
    orientedDiameterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orientedDiameterDec

end MetaMathlibExt.Complexity.NPComplete.OrientedDiameter
