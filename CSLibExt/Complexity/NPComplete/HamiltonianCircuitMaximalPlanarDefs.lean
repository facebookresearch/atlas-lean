/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on maximal planar graphs: definitions

Source:
A. Wigderson, "The complexity of the Hamiltonian circuit problem for maximal planar graphs",
Technical Report 298, EECS Department, Princeton University (1982) (the report was not
available); the result is recorded by C. Chen, "Any maximal planar graph with only one separating
triangle is Hamiltonian", Journal of Combinatorial Optimization 7(1) (2003), 79-86,
doi:10.1023/A:1021998507140 (abstract: "Chvátal and Wigderson had independently shown that the
problem of determining whether a maximal planar graph is hamiltonian is NP-complete"), and by
F. R. K. Chung, F. T. Leighton and A. L. Rosenberg, "Embedding graphs in books: a layout problem
with applications to VLSI design", SIAM Journal on Algebraic and Discrete Methods 8 (1987),
33-58, doi:10.1137/0608002;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitMaximalPlanar

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (`0 < n`, simple
edge list on `Fin n`) whose graph is maximal planar: planar, and adding an edge between any two
distinct non-adjacent vertices gives a non-planar graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ (Graph i).IsPlanar ∧
    ∀ u v : Fin i.1, u ≠ v → ¬ (Graph i).Adj u v → ¬ (Graph i ⊔ SimpleGraph.edge u v).IsPlanar

open Classical in
/-- HAMILTONIAN CIRCUIT on maximal planar graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitMaximalPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitMaximalPlanar
