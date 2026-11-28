/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on line graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
A. A. Bertossi, "The edge Hamiltonian path problem is NP-complete", Information Processing
Letters 13 (1981), 157-159, doi:10.1016/0020-0190(81)90048-X;
recorded in R. Faudree, E. Flandrin and Z. Ryjáček, "Claw-free graphs — A survey", Discrete
Mathematics 164 (1997), 87-147, doi:10.1016/S0012-365X(96)00045-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LineGraphHamiltonianCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on line graphs is NP-complete

INSTANCE: a line graph `G = (V, E)`, that is, a graph isomorphic to the line graph `L(H)` of
some finite simple graph `H` (the vertices of `L(H)` are the edges of `H`, two being adjacent
when they share an endpoint).
QUESTION: does `G` contain a Hamiltonian circuit?

Bertossi (1981) proved the problem NP-complete; Faudree, Flandrin and Ryjáček (1997) record it
as "Recognizing hamiltonian line graphs (and hence also recognizing hamiltonian claw-free graphs)
is an NP-complete problem", citing Bertossi. Line graphs are recognized, and a root graph `H`
found, in linear time (P. G. H. Lehot, "An optimal algorithm to detect a line graph and output
its root graph", Journal of the ACM 21 (1974), 569-575, doi:10.1145/321850.321853), so the
restriction does not affect membership in NP.

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian circuit needs at least three vertices).
The restriction adds that the graph is a line graph,
`MetaMathlibExt.SimpleGraph.IsLineGraph` (isomorphic to Mathlib's `SimpleGraph.lineGraph` of a
graph on some `Fin k`). Unlike `WantedExt.Complexity.NPComplete.LineGraphHamiltonianPathWanted`,
whose instance is the root graph, the instance here is the line graph itself.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT on line graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Bertossi (1981). -/
public theorem_wanted lineGraphHamiltonianCircuit_npComplete :
    lineGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lineGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.LineGraphHamiltonianCircuit
