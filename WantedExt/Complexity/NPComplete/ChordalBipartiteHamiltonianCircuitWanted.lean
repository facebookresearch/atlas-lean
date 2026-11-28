/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on chordal bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChordalBipartiteHamiltonianCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChordalBipartiteHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on chordal bipartite graphs is NP-complete

INSTANCE: a chordal bipartite graph `G = (V, E)`, that is, a bipartite graph in which every
cycle of length at least `6` has a chord.
QUESTION: does `G` contain a Hamiltonian circuit?

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple graph on
`Fin n` given by an edge list; a Hamiltonian circuit needs at least three vertices). The
restriction adds that the graph is chordal bipartite: bipartite, as Mathlib's
`SimpleGraph.IsBipartite` (`Colorable 2`), and without a chordless cycle of length at least `6`,
that is, no cycle graph `Cₖ` with `k ≥ 6` is an induced subgraph (Mathlib's
`SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`; a cycle has a chord exactly when its
vertices do not induce a cycle graph).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT on chordal bipartite graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT37]; Müller (1996). -/
public theorem_wanted chordalBipartiteHamiltonianCircuit_npComplete :
    chordalBipartiteHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chordalBipartiteHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.ChordalBipartiteHamiltonianCircuit
