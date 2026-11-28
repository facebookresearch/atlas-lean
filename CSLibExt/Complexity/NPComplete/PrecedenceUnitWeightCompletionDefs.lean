/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS4] SEQUENCING TO MINIMIZE
WEIGHTED COMPLETION TIME (comment: NP-complete in the strong sense and remains so even if all
task weights are 1);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
E. L. Lawler, "Sequencing jobs to minimize total weighted completion time subject to
precedence constraints", Annals of Discrete Mathematics 2 (1978), 75-90,
doi:10.1016/S0167-5060(08)70323-6.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitWeightCompletion

/-- An instance, as in `PrecedenceWeightedCompletionWanted`: the jobs (processing time `l(t)`,
weight `w(t)`), the precedence pairs, and the bound `K`. -/
abbrev PrecedenceUnitWeightCompletionInstance :=
  PrecedenceWeightedCompletion.PrecedenceWeightedCompletionInstance

/-- Well-formedness of an instance: the base instance is well-formed, every job has a positive
processing time and weight `1`, and `K` is positive. -/
def WellFormed (i : PrecedenceUnitWeightCompletionInstance) : Prop :=
  PrecedenceWeightedCompletion.WellFormed i ∧ (∀ j ∈ i.1, 0 < j.1 ∧ j.2 = 1) ∧ 0 < i.2.2

/-- A precedence-respecting ordering of weighted completion sum at most `K`, exactly as in
`PrecedenceWeightedCompletionWanted`. -/
def PrecedenceUnitWeightCompletionFeasible (i : PrecedenceUnitWeightCompletionInstance) :
    Prop :=
  PrecedenceWeightedCompletion.PrecedenceWeightedCompletionFeasible i

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit weights as a decision problem
over bitstrings. -/
noncomputable def precedenceUnitWeightCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitWeightCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceUnitWeightCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitWeightCompletion
