/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-connected cubic planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, the problem
restricted here;
B. Mohar, "Face covers and the genus problem for apex graphs", Journal of Combinatorial Theory,
Series B 82(1) (2001), 102-117, doi:10.1006/jctb.2000.2026, Theorem 4.1(a).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetTwoConnectedCubicPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoConnectedCubicPlanar

/-!
# INDEPENDENT SET on 2-connected cubic planar graphs is NP-complete

INSTANCE: a 2-connected cubic planar graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to the ISGCI class `2-connected ∩ cubic ∩ planar`
(`gc_1183`). 2-connected is MathlibExt's `SimpleGraph.IsVertexConnected 2` (more than 2 vertices,
and connected after deleting any single vertex), cubic is Mathlib's
`SimpleGraph.IsRegularOfDegree 3`, and planar is MathlibExt's `SimpleGraph.IsPlanar` (a
crossing-free straight-line drawing, which by Fáry's theorem exists exactly for the planar
graphs).

Mohar, Theorem 4.1(a): "The minimum vertex cover and the maximum independent set problem are
NP-hard also when restricted to 2-connected cubic planar graphs"; the graphs his reduction
outputs lie in the class, so it is a reduction to this problem. Membership in NP: the certificate
is `V'`; 2-connectivity and cubicity are checked in polynomial time, and planarity in linear time
(Hopcroft and Tarjan, "Efficient planarity testing", Journal of the ACM 21 (1974), 549-568).

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

/-- **INDEPENDENT SET on 2-connected cubic planar graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT20];
Mohar (2001), Theorem 4.1(a). -/
public theorem_wanted independentSetTwoConnectedCubicPlanar_npComplete :
    independentSetTwoConnectedCubicPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetTwoConnectedCubicPlanarDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoConnectedCubicPlanar
