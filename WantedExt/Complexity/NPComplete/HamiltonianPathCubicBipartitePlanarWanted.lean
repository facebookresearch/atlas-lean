/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on cubic bipartite planar graphs is NP-complete

Source:
A. Munaro, "On line graphs of subcubic triangle-free graphs", Discrete Mathematics 340 (2017),
1210-1226, doi:10.1016/j.disc.2017.01.006, Theorem 23 ("Hamiltonian Path is NP-complete even for
planar cubic bipartite graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathCubicBipartitePlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicBipartitePlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

/-!
# HAMILTONIAN PATH on cubic bipartite planar graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is bipartite, cubic (every vertex has
degree `3`) and planar (ISGCI class `gc_1334`, `bipartite ∩ cubic ∩ planar`).
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (endpoints
not specified)?

This is HAMILTONIAN PATH (Garey and Johnson [GT39]) restricted to planar cubic bipartite graphs;
Munaro (2017) proves it NP-complete there, by a reduction from HAMILTONIAN CYCLE THROUGH A SPECIFIED
EDGE on the same class. The instance type, the graph, the parent well-formedness condition and the
question are those of `HamiltonianPathUndirectedWanted` (`HamiltonianPathUndirectedInstance`: vertex
count and edge list on `Fin n`; `Graph`; `HamiltonianPathUndirected.WellFormed`: `0 < n` and a
simple edge list; `HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible`: a list of all
vertices without repetition whose consecutive entries are adjacent), reused unchanged; `WellFormed`
adds the class conditions. Bipartiteness is Mathlib's `SimpleGraph.IsBipartite` (2-colorable); cubic
is `SimpleGraph.IsRegularOfDegree 3`; planarity is `SimpleGraph.IsPlanar` from
`MathlibExt.Combinatorics.SimpleGraph.Planarity` (a crossing-free straight-line drawing, equivalent
to planarity for finite simple graphs by Fáry's theorem).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH on cubic bipartite planar graphs is NP-complete.** Source: Munaro (2017),
Theorem 23. -/
public theorem_wanted hamiltonianPathCubicBipartitePlanar_npComplete :
    hamiltonianPathCubicBipartitePlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathCubicBipartitePlanarDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathCubicBipartitePlanar
