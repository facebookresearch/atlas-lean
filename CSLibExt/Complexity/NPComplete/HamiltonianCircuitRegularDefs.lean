/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on k-regular graphs (fixed k ≥ 4): definitions

Source:
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131(2) (1994), 463-473, doi:10.1016/0304-3975(94)90185-6 (abstract: "for any
fixed k > 3, deciding whether a k-regular graph has a hamiltonian cycle (or path) is a
NP-complete problem");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes "4-regular" (gc_1101)
and "5-regular" (gc_1104), problem Hamiltonian cycle: NP-complete, with the reference to
Picouleau (1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRegular

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed HAMILTONIAN CIRCUIT instance
(at least one vertex, simple edge list on `Fin n`) whose graph is `k`-regular. -/
def WellFormed (k : ℕ) (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsRegularOfDegree k

open Classical in
/-- HAMILTONIAN CIRCUIT on `k`-regular graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitRegularDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitRegular
