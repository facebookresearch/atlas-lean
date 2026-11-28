/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on 5-regular graphs is NP-complete

Source:
C. Picouleau, "Complexity of the hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6 ("we prove that for
any fixed k ≥ 3, deciding whether a k-regular graph has a hamiltonian cycle (or path) is a
NP-complete problem");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH (the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianPathFiveRegularDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathFiveRegular

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
  (HamiltonianPathUndirectedInstance Graph)

/-!
# HAMILTONIAN PATH on 5-regular graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` in which every vertex has degree `5` (ISGCI
class `gc_1104`).
QUESTION: does `G` contain a Hamiltonian path, i.e. a simple path through every vertex (endpoints
not specified)?

This is HAMILTONIAN PATH (Garey and Johnson [GT39]) restricted to 5-regular graphs; Picouleau (1994)
proves it NP-complete for every fixed degree `k ≥ 3`. The instance type, the graph, the parent
well-formedness condition and the question are those of `HamiltonianPathUndirectedWanted`
(`HamiltonianPathUndirectedInstance`: vertex count and edge list on `Fin n`; `Graph`;
`HamiltonianPathUndirected.WellFormed`: `0 < n` and a simple edge list;
`HamiltonianPathUndirected.HamiltonianPathUndirectedFeasible`: a list of all vertices without
repetition whose consecutive entries are adjacent), reused unchanged; `WellFormed` adds the class
conditions. Regularity is Mathlib's `SimpleGraph.IsRegularOfDegree` (every vertex has degree `5`),
as in `PlanarFourRegularThreeColorabilityWanted` and `CubicChromaticIndexWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH on 5-regular graphs is NP-complete.** Source: Picouleau (1994). -/
public theorem_wanted hamiltonianPathFiveRegular_npComplete :
    hamiltonianPathFiveRegularDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathFiveRegularDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathFiveRegular
