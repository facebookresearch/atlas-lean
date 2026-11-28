/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for squares of graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, p. 199,
comment (3): "if G is the square of a graph", credited there to V. Chvátal (1976, private
communication);
P. Underground, "On graphs with Hamiltonian squares", Discrete Mathematics 21 (1978), 323,
doi:10.1016/0012-365X(78)90164-4 (deciding whether the square of a given graph is Hamiltonian is
NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphSquareRootDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSquares

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
the square of a graph on the same vertices. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ GraphSquareRoot.GraphSquareRootFeasible i

open Classical in
/-- HAMILTONIAN CIRCUIT for squares of graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitSquaresDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSquares
