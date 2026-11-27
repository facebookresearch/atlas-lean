/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on graphs of girth at least 9 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
M. De Biasi, answer to "Polynomial problems in graph classes defined by forbidden induced cyclic
subgraphs",
Theoretical Computer Science Stack Exchange (2014), https://cstheory.stackexchange.com/a/24882
(Theorem: "for any `k ≥ 3`, the Hamiltonian cycle problem remains NP-complete even if the graph `G`
does not contain cycles of length `≤ k`", by a gadget reduction from the planar directed case of
Papadimitriou and Vazirani); ISGCI records the result for the class `girth >= 9` (`gc_1225`),
citing this answer.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGirthNine

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on graphs of girth at least 9 is NP-complete

INSTANCE: a graph `G = (V, E)` of girth at least `9`: it has no cycle with fewer than `9`
vertices (ISGCI class `gc_1225`).
QUESTION: does `G` contain a Hamiltonian circuit?

De Biasi's theorem gives NP-completeness for graphs without cycles of length at most `k`, for every
`k ≥ 3`; the case `k = 8` is this class. The instance, its well-formedness and the question are
those of `CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple
graph on `Fin n`, `n > 0`, given by an edge list); the restriction adds `9 ≤ G.egirth`, Mathlib's
extended girth (the least length of a cycle, `⊤` for an acyclic graph), so a graph without cycles
belongs to the class. Membership in NP: the circuit is a certificate, and the girth of a graph is
computed in polynomial time (breadth-first search from every vertex).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph has
girth at least `9` (no cycle of length below `9`). -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ 9 ≤ (Graph i).egirth

open Classical in
/-- HAMILTONIAN CIRCUIT on graphs of girth at least 9 as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on graphs of girth at least 9 is NP-complete.** Source: Garey and
Johnson (1979), [GT37]; De Biasi (2014), as recorded by ISGCI. -/
public theorem_wanted hamiltonianCircuitGirthNine_npComplete :
    hamiltonianCircuitGirthNineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitGirthNineDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitGirthNine
