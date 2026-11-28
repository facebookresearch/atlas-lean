/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on planar k-regular graphs (k = 4, 5): definitions

Source:
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131(2) (1994), 463-473, doi:10.1016/0304-3975(94)90185-6 (abstract: "When the
k-regular graph is planar, deciding whether the graph has a hamiltonian cycle (or path) was
proved NP-complete for k = 3 and polynomial for k ≥ 6. We prove that for k = 4 and k = 5 the
problem is NP-complete.");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes "4-regular ∩ planar"
(gc_1103) and "5-regular ∩ planar" (gc_1106), problem Hamiltonian cycle: NP-complete, with the
reference to Picouleau (1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPlanarRegular

open HamiltonianCycleUndirected (HamiltonianCycleUndirectedInstance Graph
  HamiltonianCycleUndirectedFeasible)

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed HAMILTONIAN CIRCUIT instance
(at least one vertex, simple edge list on `Fin n`) whose graph is planar and `k`-regular. -/
def WellFormed (k : ℕ) (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsPlanar ∧ (Graph i).IsRegularOfDegree k

open Classical in
/-- HAMILTONIAN CIRCUIT on planar `k`-regular graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitPlanarRegularDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPlanarRegular
