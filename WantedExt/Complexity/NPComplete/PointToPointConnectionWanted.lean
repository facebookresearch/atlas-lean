/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POINT-TO-POINT CONNECTION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), section Graph Theory, problem MINIMUM POINT-TO-POINT CONNECTION (decision version);
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "The point-to-point delivery and connection
problems: complexity and algorithms", Discrete Appl. Math. 36 (1992), 267-292,
doi:10.1016/0166-218X(92)90258-C, Section 2 (definition) and Section 3 (all four point-to-point
connection problems are strongly NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PointToPointConnectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PointToPointConnection

/-!
# POINT-TO-POINT CONNECTION is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, sources `s₁, …, s_p` and
destinations `d₁, …, d_p`, and a positive integer `K`.
QUESTION: is there a point-to-point connection, that is, a subset `E' ⊆ E` such that each
source-destination pair `(sⱼ, dⱼ)` is connected by a path using only edges of `E'`, with
`∑_{e ∈ E'} w(e) ≤ K`?

This is the fixed-destination, undirected version (`C/f/u`) of the point-to-point connection
problem of Li, McCormick and Simchi-Levi (1992): "find a subset of arcs `A' ⊆ A` such that each
source-destination pair is connected by a path using only arcs in `A'`", with non-negative
integral costs; they prove all four versions strongly NP-hard. As in their definition, the
sources and destinations need not be distinct vertices. The vertices are `0, ..., n - 1`; the
graph is given by a simple edge list whose entries `(u, v, w)` carry the weight of the edge
`{u, v}`, and the pairs `(sⱼ, dⱼ)` are listed. A subset `E'` is a sublist of the edge list
(the list has no repeated edges); its graph is `Cslib.Complexity.Karp.edgeGraph` of its
endpoints, and "connected by a path" is `SimpleGraph.Reachable` in that graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **POINT-TO-POINT CONNECTION is NP-complete.** Source: Crescenzi and Kann, MINIMUM
POINT-TO-POINT CONNECTION; Li, McCormick and Simchi-Levi (1992). -/
public theorem_wanted pointToPointConnection_npComplete :
    pointToPointConnectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pointToPointConnectionDec

end MetaMathlibExt.Complexity.NPComplete.PointToPointConnection
