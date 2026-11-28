/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH THICKNESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN3] GRAPH
GENUS (comment: "Does `G` have thickness `K` or less" is listed as an open
generalization of planarity);
A. Mansfield, "Determining the thickness of graphs is NP-hard", Mathematical
Proceedings of the Cambridge Philosophical Society 93 (1983), 9-23,
doi:10.1017/S030500410006028X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphThickness

/-!
# GRAPH THICKNESS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`. QUESTION: does `G` have thickness
`K` or less, i.e., can `E` be partitioned into `K` disjoint sets `E₁, E₂, …, E_K` such that
each subgraph `Gᵢ = (V, Eᵢ)` is planar?

The partition is a map `f` from the edges (positions in the edge list) to `Fin K`, with
`Eᵢ = f⁻¹(i)`; under `WellFormed` the edge list has no duplicate edges in either orientation,
so positions are edges. `Gᵢ = (V, Eᵢ)` is the spanning subgraph `edgeGraph n Eᵢ` on all `n`
vertices. Planarity is the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing); by Fáry's theorem this is planarity for finite simple graphs. Each
`Gᵢ` has its own drawing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH THICKNESS is NP-complete.** Source: Garey and Johnson (1979), [OPEN3];
Mansfield (1983). -/
public theorem_wanted graphThickness_npComplete :
    graphThicknessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphThicknessDec

end MetaMathlibExt.Complexity.NPComplete.GraphThickness
