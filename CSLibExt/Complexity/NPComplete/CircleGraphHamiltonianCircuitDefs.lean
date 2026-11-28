/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on circle graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
P. Damaschke, "The Hamiltonian circuit problem for circle graphs is NP-complete",
Information Processing Letters 32 (1989), 1-2, doi:10.1016/0020-0190(89)90059-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.DominatingSetCircleGraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`. -/
abbrev CircleGraphHamiltonianCircuitInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every chord has endpoints `a < b`, and all endpoints of all
chords are distinct. -/
def WellFormed (i : CircleGraphHamiltonianCircuitInstance) : Prop :=
  (∀ c ∈ i, c.1 < c.2) ∧ (i.flatMap fun c => [c.1, c.2]).Nodup

/-- The circle graph has a Hamiltonian circuit (at least three vertices, as in
`HamiltonianCycleUndirectedFeasible`). -/
def CircleGraphHamiltonianCircuitFeasible (i : CircleGraphHamiltonianCircuitInstance) : Prop :=
  3 ≤ i.length ∧ (circleGraph i).IsHamiltonian

open Classical in
/-- HAMILTONIAN CIRCUIT on circle graphs as a decision problem over bitstrings. -/
noncomputable def circleGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircleGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ CircleGraphHamiltonianCircuitFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit
