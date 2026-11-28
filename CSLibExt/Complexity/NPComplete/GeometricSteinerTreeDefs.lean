/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC STEINER TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC
STEINER TREE;
M. R. Garey, R. L. Graham, and D. S. Johnson, "The complexity of computing
Steiner minimal trees", SIAM Journal on Applied Mathematics 32 (1977), 835-859,
doi:10.1137/0132072.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree



open GeometricTravelingSalesman (point discreteDist)

/-- An instance: the points of `P` as `((x⁺, x⁻), (y⁺, y⁻))`, standing for
`(x⁺ - x⁻, y⁺ - y⁻)`, and the bound `B` (the encoding of GEOMETRIC TRAVELING SALESMAN). -/
abbrev GeometricSteinerTreeInstance :=
  GeometricTravelingSalesman.GeometricTravelingSalesmanInstance

/-- The set `P` of the instance. -/
def points (i : GeometricSteinerTreeInstance) : Finset (ℤ × ℤ) :=
  (i.1.map point).toFinset

/-- The discretized Euclidean distance is symmetric. -/
theorem discreteDist_comm (p q : ℤ × ℤ) : discreteDist p q = discreteDist q p := by
  unfold discreteDist
  rw [show (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 by ring]

/-- The weight of an edge `{p, q}`: the discretized Euclidean distance `discreteDist p q`. -/
noncomputable def edgeLength : Sym2 (ℤ × ℤ) → ℕ :=
  Sym2.lift ⟨discreteDist, discreteDist_comm⟩

/-- Well-formedness of an instance: `0 < B`. -/
def WellFormed (i : GeometricSteinerTreeInstance) : Prop :=
  0 < i.2

open Classical in
/-- Some finite set `Q ⊆ Z × Z` and some spanning tree `T` of the points of `P ∪ Q` have total
edge weight at most `B`. -/
def GeometricSteinerTreeFeasible (i : GeometricSteinerTreeInstance) : Prop :=
  ∃ Q : Finset (ℤ × ℤ), ∃ T : SimpleGraph {x // x ∈ points i ∪ Q}, T.IsTree ∧
    ∑ e ∈ T.edgeFinset, edgeLength (e.map Subtype.val) ≤ i.2

open Classical in
/-- GEOMETRIC STEINER TREE as a decision problem over bitstrings. -/
noncomputable def geometricSteinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricSteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ GeometricSteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree
