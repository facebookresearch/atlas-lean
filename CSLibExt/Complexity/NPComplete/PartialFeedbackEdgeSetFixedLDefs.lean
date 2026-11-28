/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL FEEDBACK EDGE SET with fixed `L ≥ 3`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT9] PARTIAL
FEEDBACK EDGE SET, comment;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th
Annual ACM Symposium on Theory of Computing (1978), 253-264,
doi:10.1145/800133.804355.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartialFeedbackEdgeSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetFixedL

open MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSet

/-- An instance for a fixed cycle-length bound: vertex count `n` (vertices `Fin n`), edge list,
bound `K`. -/
abbrev FixedLInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The PARTIAL FEEDBACK EDGE SET instance given by `i` and the cycle-length bound `L`. -/
abbrev withBound (i : FixedLInstance) (L : ℕ) : PartialFeedbackEdgeSetInstance :=
  (i.1, i.2.1, i.2.2, L)

open Classical in
/-- PARTIAL FEEDBACK EDGE SET with the cycle-length bound fixed to `L`, as a decision problem
over bitstrings. -/
noncomputable def fixedLDec (L : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedLInstance) x with
  | some i => decide (WellFormed (withBound i L) ∧
      PartialFeedbackEdgeSetFeasible (withBound i L))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialFeedbackEdgeSetFixedL
