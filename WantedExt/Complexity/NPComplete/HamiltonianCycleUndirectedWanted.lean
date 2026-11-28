/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN CIRCUIT; R.
M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete

An undirected graph on vertices 0, …, n - 1, given by an explicit edge list. The question is
whether the graph has a Hamiltonian cycle: a permutation of all vertices in which consecutive
vertices, including the last and the first, are adjacent. A genuine cycle needs at least three
vertices: the two-vertex graph with one edge is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/


/-- **HAMILTONIAN CYCLE (UNDIRECTED) is NP-complete.** The decision problem HAMILTONIAN CYCLE
(UNDIRECTED) belongs to NP, and every decision problem in NP has a polynomial-time many-one
reduction to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN CIRCUIT; R. M. Karp, "Reducibility
among combinatorial problems" (1972). -/
public theorem_wanted hamiltonianCycleUndirected_npComplete :
    hamiltonianCycleUndirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCycleUndirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
