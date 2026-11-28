/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit task lengths: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 237, problem [SS4] SEQUENCING TO
MINIMIZE WEIGHTED COMPLETION TIME, comment: "NP-complete in the strong sense and remains so
even if all task lengths are 1";
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletionUnitLengths

open MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion

/-- Well-formedness of an instance of the restriction: the instance is well-formed for
`PrecedenceWeightedCompletion`, every job has processing time `1` and a positive weight, and
the bound `K` is positive. -/
def RestrictedWellFormed (i : PrecedenceWeightedCompletionInstance) : Prop :=
  WellFormed i ∧ (∀ j ∈ i.1, j.1 = 1 ∧ 0 < j.2) ∧ 0 < i.2.2

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit task lengths, as a decision
problem over bitstrings. -/
noncomputable def precedenceWeightedCompletionUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceWeightedCompletionInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ PrecedenceWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletionUnitLengths
