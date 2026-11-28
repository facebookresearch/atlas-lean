/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES with two expressions: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO10] TRUTH-FUNCTIONALLY COMPLETE
CONNECTIVES, p. 261, comment: remains NP-complete even if `|C| = 2` (reference: R. Statman
(1976), private communication).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesTwoExpressions

open MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

/-- Well-formedness of an instance: the general problem's well-formedness (every member of `C`
is an expression over `u₀, …, u_{n-1}`), and `C` consists of two distinct expressions: two
token lists whose parsed expressions differ, so two encodings of one expression count once. -/
def WellFormed (i : TruthFunctionallyCompleteConnectivesInstance) : Prop :=
  TruthFunctionallyCompleteConnectives.WellFormed i ∧ (i.2.map NonTautology.parse).Nodup ∧
    i.2.length = 2

open Classical in
/-- TRUTH-FUNCTIONALLY COMPLETE CONNECTIVES with `|C| = 2`, as a decision problem over
bitstrings. -/
noncomputable def twoExpressionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TruthFunctionallyCompleteConnectivesInstance) x with
  | some i => decide (WellFormed i ∧ TruthFunctionallyCompleteConnectivesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesTwoExpressions
