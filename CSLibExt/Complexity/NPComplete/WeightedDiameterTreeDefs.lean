/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER on trees: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205
(comment: "NP-complete in the strong sense, even if `G` is a tree.");
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.WeightedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterTree

open WeightedDiameter (WeightedDiameterInstance Graph WeightedDiameterFeasible)

/-- Well-formedness of an instance: the parent's (a simple edge list in range, `C` with `|E|`
members, `K` positive), and the graph is a tree. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  WeightedDiameter.WellFormed i ∧ (Graph i).IsTree

open Classical in
/-- WEIGHTED DIAMETER on trees as a decision problem over bitstrings. -/
noncomputable def weightedDiameterTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterTree
