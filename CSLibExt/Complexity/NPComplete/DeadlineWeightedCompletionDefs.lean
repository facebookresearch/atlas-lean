/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH DEADLINES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS4] SEQUENCING TO MINIMIZE
WEIGHTED COMPLETION TIME, p. 237, comment ("If the partial order < is replaced by individual
task deadlines, the resulting problem is NP-complete in the strong sense [Lenstra, 1977]");
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(b) (`n|1|L_max ≤ 0|Σw_jC_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlineWeightedCompletion

open SequencingToMinimizeWeightedTardiness in
/-- Some one-processor schedule `σ` meets every deadline, `σ(t) + l(t) ≤ d(t)`, and has
weighted completion time `∑ t, (σ(t) + l(t)) · w(t)` at most `K`. -/
def DeadlineWeightedCompletionFeasible (i : SequencingToMinimizeWeightedTardinessInstance) :
    Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    (∀ t, σ t + taskLength i t ≤ deadline i t) ∧
    ∑ t, (σ t + taskLength i t) * weight i t ≤ i.2

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH DEADLINES as a decision problem over
bitstrings. -/
noncomputable def deadlineWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeWeightedTardiness.SequencingToMinimizeWeightedTardinessInstance)
      x with
  | some i => decide (SequencingToMinimizeWeightedTardiness.WellFormed i ∧
      DeadlineWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeadlineWeightedCompletion
