/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECISION TREE (tests with at most three positives): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS15] DECISION TREE
(comment: remains NP-complete even if each test is `1` on at most three objects);
L. Hyafil and R. L. Rivest, "Constructing optimal binary decision trees is
NP-complete", Information Processing Letters 5 (1976), 15-17,
doi:10.1016/0020-0190(76)90095-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DecisionTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecisionTreeThreePositives

/-- Well-formedness of an instance: a well-formed DECISION TREE instance in which every test
is `1` on at most three objects. -/
def WellFormed (i : DecisionTree.DecisionTreeInstance) : Prop :=
  DecisionTree.WellFormed i ∧ ∀ T ∈ i.2.1, T.count true ≤ 3

open Classical in
/-- DECISION TREE (tests with at most three positives) as a decision problem over
bitstrings. -/
noncomputable def decisionTreeThreePositivesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecisionTree.DecisionTreeInstance) x with
  | some i => decide (WellFormed i ∧ DecisionTree.DecisionTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DecisionTreeThreePositives
