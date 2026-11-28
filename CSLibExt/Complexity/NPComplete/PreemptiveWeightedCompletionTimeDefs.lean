/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, comment on p. 240 ("These results continue to hold if "preemptive"
schedules are allowed [McNaughton, 1959]"), with preemptive schedules as in [SS12];
R. McNaughton, "Scheduling with deadlines and loss functions", Management Science 6 (1959),
1-12, doi:10.1287/mnsc.6.1.1;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTime

open MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance Task taskLength weight)

/-- The pieces of every task form a preemptive subdivision: each piece `(s, d)` (start `s`,
length `d`) has `d > 0`, the lengths of a task's pieces sum to its length, and each piece starts
no earlier than the previous piece of the same task ends. -/
def IsPreemptiveSubdivision (i : SchedulingToMinimizeWeightedCompletionTimeInstance)
    (pieces : Task i → List (ℕ × ℕ)) : Prop :=
  ∀ t, (∀ p ∈ pieces t, 0 < p.2) ∧ ((pieces t).map Prod.snd).sum = taskLength i t ∧
    (pieces t).IsChain fun p q => p.1 + p.2 ≤ q.1

/-- The number of pieces, over all tasks, running at time `u`. -/
def runningPieces (i : SchedulingToMinimizeWeightedCompletionTimeInstance)
    (pieces : Task i → List (ℕ × ℕ)) (u : ℕ) : ℕ :=
  ∑ t, (pieces t).countP fun p => p.1 ≤ u ∧ u < p.1 + p.2

/-- The completion time of task `t`: the end of its last piece. -/
def completionTime (i : SchedulingToMinimizeWeightedCompletionTimeInstance)
    (pieces : Task i → List (ℕ × ℕ)) (t : Task i) : ℕ :=
  (((pieces t).getLast?).map fun p => p.1 + p.2).getD 0

/-- Some `m`-processor preemptive schedule has weighted sum of completion times at most `K`. -/
def PreemptiveWeightedCompletionTimeFeasible
    (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Prop :=
  ∃ pieces : Task i → List (ℕ × ℕ), IsPreemptiveSubdivision i pieces ∧
    (∀ u, runningPieces i pieces u ≤ i.1) ∧
    ∑ t, completionTime i pieces t * weight i t ≤ i.2.2

open Classical in
/-- PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME as a decision problem over
bitstrings. -/
noncomputable def preemptiveWeightedCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingToMinimizeWeightedCompletionTimeInstance) x with
  | some i => decide (SchedulingToMinimizeWeightedCompletionTime.WellFormed i ∧
      PreemptiveWeightedCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTime
