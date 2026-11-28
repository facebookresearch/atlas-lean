/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on planar cubic graphs is NP-complete

Source:
M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed,
"Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete
Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoCliquesCubicPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCubicPlanar

open PartitionIntoCliques (PartitionIntoCliquesInstance Graph PartitionIntoCliquesFeasible)

/-!
# PARTITION INTO CLIQUES on planar cubic graphs is NP-complete

INSTANCE: a planar cubic graph `G = (V, E)` (every vertex has degree exactly 3) and a positive
integer `K ≤ |V|`.
QUESTION: can `V` be partitioned into `k ≤ K` disjoint sets `V₁, …, V_k` such that each `Vᵢ`
induces a complete subgraph of `G`?

This is PARTITION INTO CLIQUES ([GT15], `PartitionIntoCliquesDefs`) restricted to the graph
class `cubic ∩ planar` of the ISGCI database. Cerioli, Faria, Ferreira, Martinhon, Protti and
Reed (2008) establish the NP-completeness of partition into cliques for planar cubic graphs.

The instance, the graph, the well-formedness `0 < K ≤ |V|` and the question are those of
`PartitionIntoCliquesDefs`; the restriction adds to the well-formedness that the graph is
planar, the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line
drawing; by Fáry's theorem this is the usual notion for simple graphs), and cubic, Mathlib's
`SimpleGraph.IsRegularOfDegree 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO CLIQUES on planar cubic graphs is NP-complete.** Source: Cerioli, Faria,
Ferreira, Martinhon, Protti and Reed (2008); Garey and Johnson (1979), [GT15]. -/
public theorem_wanted partitionIntoCliquesCubicPlanar_npComplete :
    partitionIntoCliquesCubicPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoCliquesCubicPlanarDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCubicPlanar
