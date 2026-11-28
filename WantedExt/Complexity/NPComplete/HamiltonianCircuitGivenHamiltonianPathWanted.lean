/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (comment:
NP-complete even if a Hamiltonian path for `G` is given as part of the instance);
C. H. Papadimitriou and K. Steiglitz, "On the complexity of local search for the traveling
salesman problem", SIAM Journal on Computing 6(1) (1977), 76-83, doi:10.1137/0206005.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath

/-!
# HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete

An instance is a graph `G = (V, E)` together with a Hamiltonian path of `G`. The question is
whether `G` contains a Hamiltonian circuit, a simple cycle through every vertex exactly once.
Papadimitriou and Steiglitz (1977) proved that knowing a Hamiltonian path does not help: the
problem stays NP-complete, which they used to show that polynomial local search for the
traveling salesman problem cannot guarantee near-optimal tours unless `P = NP`.

The graph is simple and given by an edge list on `Fin n`. The Hamiltonian path is a list of
vertices that visits each of `0, …, n - 1` exactly once, consecutive entries being adjacent;
that it is a Hamiltonian path of `G` is part of the instance class (`WellFormed`). A
Hamiltonian circuit is Mathlib's `SimpleGraph.Walk.IsHamiltonianCycle`: a cycle (so at least
three vertices) visiting every vertex exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT given a Hamiltonian path is NP-complete.** Source: Garey and Johnson
(1979), [GT37]; Papadimitriou and Steiglitz (1977). -/
public theorem_wanted hamiltonianCircuitGivenHamiltonianPath_npComplete :
    hamiltonianCircuitGivenHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitGivenHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGivenHamiltonianPath
