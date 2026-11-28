/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for grid graphs: definitions

Source:
B. N. Clark, C. J. Colbourn and D. S. Johnson, "Unit disk graphs", Discrete Mathematics
86(1-3) (1990), 165-177, doi:10.1016/0012-365X(90)90358-O;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs
public import CSLibExt.Complexity.NPComplete.GridGraphHamiltonianCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetGridGraphs

open MetaMathlibExt.Complexity.NPComplete.GridGraphHamiltonianCircuit
  (GridGraphHamiltonianCircuitInstance gridEdges)

/-- An instance: the points of `V` (each a pair of integer coordinates, each coordinate an
integer `a - b` given as the pair `(a, b)`) and the bound `K`. -/
abbrev DominatingSetGridGraphsInstance := GridGraphHamiltonianCircuitInstance × ℕ

/-- The grid graph and the bound as a DOMINATING SET instance: `|V|` vertices, the grid edges,
and `K`. -/
def toDominatingSetInstance (i : DominatingSetGridGraphsInstance) :
    DominatingSet.DominatingSetInstance :=
  (i.1.length, gridEdges i.1, i.2)

/-- Well-formedness of an instance: the listed points are pairwise distinct (`V` is a set), and
`0 < K ≤ |V|`. -/
def WellFormed (i : DominatingSetGridGraphsInstance) : Prop :=
  GridGraphHamiltonianCircuit.WellFormed i.1 ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

open Classical in
/-- DOMINATING SET for grid graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetGridGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetGridGraphsInstance) x with
  | some i =>
    decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible (toDominatingSetInstance i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetGridGraphs
