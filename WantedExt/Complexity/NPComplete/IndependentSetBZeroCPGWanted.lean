/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on B₀-CPG graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
N. Champseix, E. Galby, A. Munaro and B. Ries, "CPG graphs: Some structural and hardness
results", Discrete Applied Mathematics 290 (2021), 17-35, doi:10.1016/j.dam.2020.11.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetBZeroCPGDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetBZeroCPG

/-!
# INDEPENDENT SET on B₀-CPG graphs is NP-complete

INSTANCE: a `B₀-CPG` graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to the class `B₀-CPG` (ISGCI `gc_1337`): contact
graphs of pairwise interiorly disjoint horizontal or vertical segments on a grid, two vertices
being adjacent exactly when their segments touch. The class is
`PartitionIntoCliquesBZeroCPG.IsBZeroCPG` from
`WantedExt.Complexity.NPComplete.PartitionIntoCliquesBZeroCPGWanted` (see that module for the
segment encoding and the test for common interior points); the segment model is not part of the
input.

Champseix, Galby, Munaro and Ries show that Independent Set remains NP-hard for `B₀-CPG` graphs
(abstract: "Independent Set and Clique Cover remain NP-hard for B₀-CPG graphs"); their
reduction outputs `B₀-CPG` graphs, so it is a reduction to this problem. Membership in NP: the
vertex count `n` is written in binary, so the vertices occurring in no listed edge (isolated
vertices) may be exponentially many and are not listed in the certificate. An isolated vertex can
be added to or removed from a `B₀-CPG` model without affecting the other segments (as a unit
segment outside the bounding box of all others), so `G` is `B₀-CPG` exactly when its subgraph
`G'` induced on the vertices occurring in edges is, and the independence number of `G` is that of
`G'` plus the number of isolated vertices. The certificate is a segment model of `G'`, with
endpoints compressed to their ranks among all endpoint coordinates (this changes no contact and no
interior intersection), and an independent set `S'` of `G'` with
`|S'| + (n - |V(G')|) ≥ K`; it has size polynomial in the edge list and is checked in polynomial
time in the input length.

The instance, the graph and the question follow
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`: a vertex count `n`
(vertices `Fin n`), an edge list and the bound `K`; the independent set is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET on B₀-CPG graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20];
Champseix, Galby, Munaro and Ries (2021). -/
public theorem_wanted independentSetBZeroCPG_npComplete :
    independentSetBZeroCPGDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetBZeroCPGDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetBZeroCPG
