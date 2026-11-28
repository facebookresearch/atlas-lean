/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CAPACITATED SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND6] GEOMETRIC CAPACITATED SPANNING
TREE (reference [Papadimitriou, 1976c], transformation from X3C);
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree

/-!
# GEOMETRIC CAPACITATED SPANNING TREE is NP-complete

INSTANCE: a set `P ⊆ Z × Z` of points in the plane, a specified point `p₀ ∈ P`, a requirement
`r(p) ∈ Z₀⁺` for each `p ∈ P - p₀`, a capacity `c ∈ Z⁺`, and a bound `B ∈ Z⁺`. QUESTION: is
there a spanning tree `T = (P, E')` for the complete graph `G = (P, E)` such that
`∑_{e ∈ E'} d(e) ≤ B`, where `d((x₁, y₁), (x₂, y₂))` is the discretized Euclidean distance
`⌈((x₁ - x₂)² + (y₁ - y₂)²)^(1/2)⌉`, and such that for each `e ∈ E'`, if `U(e)` is the set of
vertices whose paths to `p₀` pass through `e`, then `∑_{u ∈ U(e)} r(u) ≤ c`?

The points are listed as in GEOMETRIC TRAVELING SALESMAN
(`WantedExt.Complexity.NPComplete.GeometricTravelingSalesmanWanted`): each coordinate is a pair
`(p, q)` of naturals standing for `p - q`, and the points must be distinct. The distance is that
module's `discreteDist`. Points are indexed by their position `Fin m` in the list; `p₀` is
given by its index. A spanning tree of the complete graph on `P` is any `SimpleGraph` `T` on
`Fin m` with `T.IsTree` (Mathlib); its edge sum counts each edge `{a, b}` once, as the
summand for `a < b`. As in `CapacitatedSpanningTreeWanted`, the path from `u` to `p₀` in `T`
is a `SimpleGraph.Walk` with `IsPath` (unique in a tree), so `u ∈ U(e)` is stated as "some path
from `u` to `p₀` in `T` contains `e`". The requirement list has one entry per point; the entry
of `p₀` is never read, since `p₀ ∉ U(e)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GEOMETRIC CAPACITATED SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979),
[ND6]; Papadimitriou (1978). -/
public theorem_wanted geometricCapacitatedSpanningTree_npComplete :
    geometricCapacitatedSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geometricCapacitatedSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTree
