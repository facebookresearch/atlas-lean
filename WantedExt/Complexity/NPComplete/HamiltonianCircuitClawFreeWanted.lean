/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for claw-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
A. A. Bertossi, "The edge Hamiltonian path problem is NP-complete", Information Processing
Letters 13 (1981), 157-159, doi:10.1016/0020-0190(81)90048-X (line graphs, which are claw-free);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021,
Table 1 (HAM CIRC on CLAW-FREE: N).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitClawFree

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`). QUESTION: does `G` contain a
Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37], stated on `main` as
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted`) restricted to claw-free graphs.
Johnson's 1985 table (NP-completeness column 16) and its 2022 revision list it as NP-complete:
Bertossi (1981) proves HAMILTONIAN CIRCUIT NP-complete for line graphs (stated on `main` as
`LineGraphHamiltonianCircuitWanted`), and every line graph is claw-free. The instance type, the
graph, the parent's well-formedness (at least one vertex, simple edge list on `Fin n`) and the
question (`3 ≤ n` and Mathlib's `SimpleGraph.IsHamiltonian`) are the parent's; the restriction
adds claw-freeness to `WellFormed`.
Claw-freeness is the repository's predicate `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`):
no vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, i.e. no induced
`K₁,₃`.

Membership in NP holds for all graphs, and claw-freeness is checked in `O(n⁴)` time. A graph
with an isolated vertex and more than one vertex has no Hamiltonian circuit, and isolated
vertices are claw-free, so the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex, simple edge list on `Fin n`) whose graph is claw-free. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsClawFree

open Classical in
/-- HAMILTONIAN CIRCUIT for claw-free graphs as a decision problem
over bitstrings. -/
noncomputable def hamiltonianCircuitClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT for claw-free graphs is NP-complete.**
Source: Garey and Johnson (1979), [GT37]; Bertossi (1981). -/
public theorem_wanted hamiltonianCircuitClawFree_npComplete :
    hamiltonianCircuitClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitClawFree
