/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem) [...], and if, in
addition, no vertex has degree exceeding 3");
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th Annual ACM
Symposium on Theory of Computing (1978), 253-264, doi:10.1145/800133.804355.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev SimpleMaxCutDegreeThreeInstance := MaxCutInstance

open Classical in
/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph has no vertex of degree exceeding 3, and `0 < K`. -/
def WellFormed (i : SimpleMaxCutDegreeThreeInstance) : Prop :=
  MaxCut.WellFormed i ∧ (∀ v, (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).degree v ≤ 3) ∧
    0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutDegreeThreeFeasible (i : SimpleMaxCutDegreeThreeInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on graphs of maximum degree 3 as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleMaxCutDegreeThreeInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutDegreeThreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutDegreeThree
