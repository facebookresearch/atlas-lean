/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on 4-regular planar graphs is NP-complete

Source:
C. Picouleau, "Complexity of the hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6 ("When the k-regular
graph is planar, deciding whether the graph has a hamiltonian cycle (or path) was proved
NP-complete for k = 3 and polynomial for k ≥ 6. We prove that for k = 4 and k = 5 the problem
is NP-complete");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathFourRegularPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathFourRegularPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

/-!
# HAMILTONIAN PATH on 4-regular planar graphs is NP-complete

INSTANCE: a finite simple undirected planar graph `G = (V, E)` in which every vertex has degree `4`
(ISGCI class `gc_1103`, `4-regular ∩ planar`).
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (endpoints
not specified)?

This is HAMILTONIAN PATH (Garey and Johnson [GT39]) restricted to 4-regular planar graphs; Picouleau
(1994) proves it NP-complete for planar `k`-regular graphs with `k = 4` and `k = 5`. The instance
type, the graph, the parent well-formedness condition and the question are those of
`HamiltonianPathUndirectedWanted` (`HamiltonianPathUndirectedInstance`: vertex count and edge list
on `Fin n`; `Graph`; `HamiltonianPathUndirected.WellFormed`: `0 < n` and a simple edge list;
`HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible`: a list of all vertices without
repetition whose consecutive entries are adjacent), reused unchanged; `WellFormed` adds the class
conditions. Regularity is Mathlib's `SimpleGraph.IsRegularOfDegree`; planarity is
`SimpleGraph.IsPlanar` from `MathlibExt.Combinatorics.SimpleGraph.Planarity` (a crossing-free
straight-line drawing, equivalent to planarity for finite simple graphs by Fáry's theorem), as in
`PlanarFourRegularThreeColorabilityWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH on 4-regular planar graphs is NP-complete.** Source: Picouleau (1994). -/
public theorem_wanted hamiltonianPathFourRegularPlanar_npComplete :
    hamiltonianPathFourRegularPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathFourRegularPlanarDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathFourRegularPlanar
