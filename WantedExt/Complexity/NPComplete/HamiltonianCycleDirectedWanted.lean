/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CYCLE (DIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN CIRCUIT
(directed); R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleDirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleDirected

/-!
# HAMILTONIAN CYCLE (DIRECTED) is NP-complete

A directed graph on vertices 0, …, n - 1, given by an explicit arc list. The question is
whether the graph has a directed Hamiltonian cycle: a permutation of all vertices in which
consecutive vertices, including the last and the first, are joined by arcs in the forward
direction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CYCLE (DIRECTED) is NP-complete.** The decision problem HAMILTONIAN CYCLE
(DIRECTED) belongs to NP, and every decision problem $L$ in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN CIRCUIT (directed); R. M. Karp,
"Reducibility among combinatorial problems" (1972). -/
public theorem_wanted hamiltonianCycleDirected_npComplete :
    hamiltonianCycleDirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCycleDirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleDirected
