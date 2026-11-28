/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most k (fixed k ≥ 1) is: definitions
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment
("Remains NP-complete if all edge weights are equal, even if [...] G is planar [Garey and
Johnson, 1977a]");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, unweighted STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphThicknessDefs
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeThickness

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- The GRAPH THICKNESS instance with the same vertex count, the edge list without weights, and
the bound `k`. -/
def withThickness (k : ℕ) (i : SteinerTreeInstance) : GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1.map fun e => (e.1, e.2.1), k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: it is a well-formed
STEINER TREE IN GRAPHS instance, every edge has weight `1`, its graph has thickness at most `k`,
it has at least one vertex, and the bound `B` is positive. -/
def WellFormed (k : ℕ) (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    GraphThickness.GraphThicknessFeasible (withThickness k i) ∧ 0 < i.1 ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most `k`, for the fixed `k`,
as a decision problem over bitstrings. -/
noncomputable def steinerTreeThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed k i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeThickness
