/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH HOMOMORPHISM onto a triangle is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT52] GRAPH HOMOMORPHISM, p. 203,
comment: "Remains NP-complete for H fixed to be a triangle" (no separate attribution; the entry
cites L. A. Levin, "Universal sequential search problems", Problemy Peredachi Informatsii 9(3)
(1973), 115-116, for the problem with `H` part of the instance).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphHomomorphismIdentificationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismTriangle

open MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismIdentification

/-!
# GRAPH HOMOMORPHISM onto a triangle is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: can a graph isomorphic to the triangle `K₃` be obtained
from `G` by a sequence of identifications of non-adjacent vertices, where each step replaces two
non-adjacent vertices `u, v` by a single vertex `w` adjacent to exactly those vertices that were
previously adjacent to at least one of `u` and `v`?

This is [GT52] GRAPH HOMOMORPHISM
(`WantedExt.Complexity.NPComplete.GraphHomomorphismIdentificationWanted`) with `H` fixed to be
the triangle, as in Garey and Johnson's comment. The instance is `G` alone (vertex count and
edge list); `withTriangle` pairs it with the triangle on `Fin 3` given by the edge list
`[(0, 1), (0, 2), (1, 2)]`, and well-formedness and the question are those of the parent for
that pair: `G` is a simple graph, and some surjective map `f : V → Fin 3` has fibers that are
independent sets of `G` and quotient `G.map f` equal to the triangle. Equivalently, `G` has a
proper 3-coloring that uses all three colors and has an edge between every two color classes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count and edge list of `G`. -/
abbrev GraphHomomorphismTriangleInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH HOMOMORPHISM instance with graph `G` and `H` the triangle on `Fin 3`. -/
abbrev withTriangle (i : GraphHomomorphismTriangleInstance) :
    GraphHomomorphismIdentificationInstance :=
  (i.1, i.2, 3, [(0, 1), (0, 2), (1, 2)])

open Classical in
/-- GRAPH HOMOMORPHISM onto a triangle as a decision problem over bitstrings. -/
noncomputable def graphHomomorphismTriangleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphHomomorphismTriangleInstance) x with
  | some i => decide (GraphHomomorphismIdentification.WellFormed (withTriangle i) ∧
      GraphHomomorphismIdentificationFeasible (withTriangle i))
  | none => false

/-- **GRAPH HOMOMORPHISM onto a triangle is NP-complete.** Source: Garey and Johnson (1979),
[GT52], comment. -/
public theorem_wanted graphHomomorphismTriangle_npComplete :
    graphHomomorphismTriangleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphHomomorphismTriangleDec

end MetaMathlibExt.Complexity.NPComplete.GraphHomomorphismTriangle
