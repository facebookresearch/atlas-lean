/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on graphs of thickness at most k (fixed k ≥ 1): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, comment
("Remains NP-complete (1) if G is planar, cubic, 3-connected, and has no face with fewer than 5
edges [Garey, Johnson, and Tarjan, 1976a]");
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5(4) (1976), 704-714, doi:10.1137/0205049;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, HAMILTONIAN CIRCUIT: NP-complete, citing Garey and Johnson).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThickness

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : HamiltonianCycleUndirectedInstance) :
    GraphThickness.GraphThicknessInstance :=
  (i.1, i.2, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed HAMILTONIAN
CIRCUIT instance (a simple edge list on `Fin n`, `n > 0`) whose graph has thickness at most
`k`. -/
def WellFormed (k : ℕ) (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧
    GraphThickness.GraphThicknessFeasible (withThickness k i)

open Classical in
/-- HAMILTONIAN CIRCUIT on graphs of thickness at most `k`, for the fixed `k`, as a decision
problem over bitstrings. -/
noncomputable def hamiltonianCircuitThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitThickness
