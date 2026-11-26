/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH DEADLINES is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeadlineWeightedCompletion

/-!
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH DEADLINES is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a weight
`w(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `σ` for `T` that meets every deadline, `σ(t) + l(t) ≤ d(t)` for all
`t ∈ T`, and for which the sum, over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)` is `K` or less?

This is Garey and Johnson's [SS4] with the partial order replaced by individual task deadlines
(`1|d̄_j|Σw_jC_j`), as in the comment to [SS4]; a one-processor schedule and the meaning of
meeting a deadline are those of [SS1]. The instance (task triples `(l(t), w(t), d(t))` and `K`),
the task accessors, `WellFormed` (all lengths, weights, deadlines and `K` positive) and
`IsOneProcessorSchedule` (a one-to-one `σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying
`σ(t) ≥ σ(t') + l(t')`) are those of `SequencingToMinimizeWeightedTardinessDefs` ([SS5]),
whose instance class is the same. Lenstra, Rinnooy Kan and Brucker (1977) prove
NP-completeness by a reduction from KNAPSACK; Garey and Johnson record strong
NP-completeness. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME WITH DEADLINES is NP-complete.** Source:
Garey and Johnson (1979), [SS4], comment; Lenstra, Rinnooy Kan, and Brucker (1977),
Theorem 4(b). -/
public theorem_wanted deadlineWeightedCompletion_npComplete :
    deadlineWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deadlineWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.DeadlineWeightedCompletion
