/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is cubic (every vertex has degree
exactly 3) and planar (ISGCI class `gc_1102`, cubic ∩ planar).
QUESTION: does `G` contain a Hamiltonian circuit, i.e. a simple cycle through every vertex?

This is HAMILTONIAN CIRCUIT (Garey and Johnson [GT37]) restricted to planar cubic graphs. Garey,
Johnson and Tarjan prove the problem NP-complete for planar, cubic, triply-connected graphs, and
note that it is therefore intractable for "any larger class containing all such graphs"; their
reduction produces planar cubic graphs, so it proves this restriction NP-hard. Membership in NP is
immediate (the circuit is a certificate).

Cubic means 3-regular: the cubic restriction is HAMILTONIAN CIRCUIT on `k`-regular graphs
(`HamiltonianCircuitRegularWanted`) at `k = 3`, whose well-formedness
(`HamiltonianCircuitRegular.WellFormed 3`: a well-formed HAMILTONIAN CIRCUIT instance, `0 < n` and a
simple edge list, whose graph is Mathlib's `SimpleGraph.IsRegularOfDegree 3`) is reused; the
instance, the graph and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirectedDefs`: `HamiltonianCycleUndirected.Graph` and
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible`, `3 ≤ n` and Mathlib's
`SimpleGraph.IsHamiltonian`). The restriction adds that the graph is planar, MathlibExt's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem is equivalent
to planarity).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Garey, Johnson and Tarjan (1976). -/
public theorem_wanted hamiltonianCircuitCubicPlanar_npComplete :
    hamiltonianCircuitCubicPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitCubicPlanarDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanar
