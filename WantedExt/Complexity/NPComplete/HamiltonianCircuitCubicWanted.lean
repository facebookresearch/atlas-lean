/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON CUBIC GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCircuitRegularWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubic

/-!
# HAMILTONIAN CIRCUIT ON CUBIC GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is cubic (every vertex has degree
exactly 3; ISGCI class `gc_1100`).
QUESTION: does `G` contain a Hamiltonian circuit, i.e. a simple cycle through every vertex?

This is HAMILTONIAN CIRCUIT (Garey and Johnson [GT37]) restricted to cubic graphs. Garey, Johnson
and Tarjan prove the problem NP-complete for planar, cubic, triply-connected graphs, and note that
it is therefore intractable for "any larger class containing all such graphs"; their reduction
produces cubic graphs, so it proves this restriction NP-hard. Membership in NP is immediate (the
circuit is a certificate).

Cubic means 3-regular, so this is the case `k = 3` of HAMILTONIAN CIRCUIT on `k`-regular graphs
(`HamiltonianCircuitRegularWanted`), whose decision problem
`HamiltonianCircuitRegular.hamiltonianCircuitRegularDec 3` is stated NP-complete below. That
module's theorem covers `k ≥ 4` (Picouleau); `k = 3` rests on Garey, Johnson and Tarjan. Its
instance, graph and question are those of HAMILTONIAN CIRCUIT (`HamiltonianCycleUndirectedWanted`: a
vertex count and a simple edge list on `Fin n`, and `3 ≤ n` with Mathlib's
`SimpleGraph.IsHamiltonian`), and its well-formedness `HamiltonianCircuitRegular.WellFormed 3` adds
Mathlib's `SimpleGraph.IsRegularOfDegree 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT ON CUBIC GRAPHS is NP-complete**: HAMILTONIAN CIRCUIT on `k`-regular
graphs for `k = 3`. Source: Garey and Johnson (1979), [GT37]; Garey, Johnson and Tarjan (1976). -/
public theorem_wanted hamiltonianCircuitCubic_npComplete :
    HamiltonianCircuitRegular.hamiltonianCircuitRegularDec 3 ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            (HamiltonianCircuitRegular.hamiltonianCircuitRegularDec 3)

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubic
