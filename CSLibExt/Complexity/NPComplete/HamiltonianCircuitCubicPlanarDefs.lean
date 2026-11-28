/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, the problem
restricted here;
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HamiltonianCircuitRegularDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance on a `3`-regular
graph (`0 < n`, simple edge list, every vertex of degree 3) whose graph is planar. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCircuitRegular.WellFormed 3 i ∧ (Graph i).IsPlanar

open Classical in
/-- HAMILTONIAN CIRCUIT ON PLANAR CUBIC GRAPHS as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitCubicPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitCubicPlanar
