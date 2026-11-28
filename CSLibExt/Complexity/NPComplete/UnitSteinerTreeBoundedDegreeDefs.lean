/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree `k`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS,
pp. 208-209 (the problem; NP-complete with equal edge weights, even for planar graphs);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451,
doi:10.1016/0196-6774(85)90012-4, Table 1 (unweighted STEINER TREE IN GRAPHS is NP-complete for
degree-`k` graphs, `k` fixed, and for grid graphs, the latter citing Garey and Johnson 1977);
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM J.
Appl. Math. 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitSteinerTreeBoundedDegree

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

open Classical in
/-- Well-formedness of an instance for the degree bound `k`: a well-formed STEINER TREE IN GRAPHS
instance with every edge weight `1`, every vertex of degree at most `k`, and `0 < B`. -/
def WellFormed (k : ℕ) (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (∀ v, (SteinerTree.Graph i i.2.1).degree v ≤ k) ∧
    0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree `k`, as a decision
problem over bitstrings. -/
noncomputable def unitSteinerTreeBoundedDegreeDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed k i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitSteinerTreeBoundedDegree
