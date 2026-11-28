/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4;
A. A. Bertossi and M. A. Bonuccelli, "Hamiltonian circuits in interval graph generalizations",
Information Processing Letters 23 (1986), 195-200, doi:10.1016/0020-0190(86)90135-3;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitChordalGraphs

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on chordal graphs is NP-complete

INSTANCE: a chordal graph `G = (V, E)`, that is, a graph in which every cycle of length at least
`4` has a chord.
QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT (Garey and Johnson [GT37]) restricted to chordal graphs. Müller
(1996, abstract) proves it NP-complete on chordal bipartite graphs and adds: "As a corollary,
HAMILTONIAN CIRCUIT is NP-complete for strongly chordal split graphs" (recorded with this quote by
`StronglyChordalSplitHamiltonianPathWanted`). Bertossi and Bonuccelli prove it NP-complete on
undirected path graphs (`UndirectedPathGraphHamiltonianCircuitWanted`). Strongly chordal split
graphs and undirected path graphs are chordal, so the chordal case follows. de Figueiredo,
de Melo, Sasaki and Silva (Table 1, row CHORDAL, column HAM CIR) list the problem as
NP-complete, citing Müller (1996).

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; `HamiltonianCycleUndirectedFeasible` asks for at least
three vertices and Mathlib's `SimpleGraph.IsHamiltonian`). The restriction adds that the graph is
chordal, stated as in `PathwidthChordalGraphsWanted` and `DominatingSetChordalGraphsWanted`: no
cycle graph `Cₖ` with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`; a cycle has a chord exactly when its vertices do not induce a cycle
graph).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT on chordal graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Müller (1996); Bertossi and Bonuccelli (1986). -/
public theorem_wanted hamiltonianCircuitChordalGraphs_npComplete :
    hamiltonianCircuitChordalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitChordalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitChordalGraphs
