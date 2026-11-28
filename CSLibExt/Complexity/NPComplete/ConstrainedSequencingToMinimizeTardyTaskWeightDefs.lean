/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT;
D. Zuckerman, "On unapproximable versions of NP-complete problems", SIAM Journal on Computing
25 (1996), 1293-1304, doi:10.1137/S0097539794266407, Theorem 3.1, problem 19 (CONSTRAINED MAX
JOB SEQUENCING); conference version: Proc. 8th Annual Structure in Complexity Theory Conference
(1993), 305-312, doi:10.1109/SCT.1993.336517;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS3] SEQUENCING TO MINIMIZE TARDY TASK WEIGHT
(the unconstrained problem, an antecedent);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (JOB SEQUENCING, the unconstrained problem, an antecedent).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.WeightedTardyJobs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

open WeightedTardyJobs (WeightedTardyJobsInstance WeightedTardy)

/-- An instance: the tasks (length, deadline, weight) and the tardy-weight bound `K`
(`WeightedTardyJobs`'s instance), the subset `S`, and the bound `J`. -/
abbrev ConstrainedSequencingInstance := WeightedTardyJobsInstance × List ℕ × ℕ

/-- One task's effect on (elapsed time, number of tasks of `S` completed by their deadlines). -/
def onTimeStep (tasks : List (ℕ × ℕ × ℕ)) (S : List ℕ) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (tasks.getD j (0, 0, 0)).1
  (t, state.2 + if j ∈ S ∧ t ≤ (tasks.getD j (0, 0, 0)).2.1 then 1 else 0)

/-- The number of tasks of `S` completed by their deadlines when the tasks run in `order`. -/
def onTimeInS (tasks : List (ℕ × ℕ × ℕ)) (S : List ℕ) (order : List ℕ) : ℕ :=
  (order.foldl (onTimeStep tasks S) (0, 0)).2

/-- Well-formedness of an instance: every length, deadline and weight is positive, `K` is
positive, the elements of `S` are task indices, and `J` is positive. -/
def WellFormed (i : ConstrainedSequencingInstance) : Prop :=
  (∀ t ∈ i.1.1, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2) ∧ 0 < i.1.2 ∧
    (∀ j ∈ i.2.1, j < i.1.1.length) ∧ 0 < i.2.2

/-- Some ordering of the tasks has tardy weight at most `K` and completes at least `J` tasks of
`S` by their deadlines. -/
def ConstrainedSequencingFeasible (i : ConstrainedSequencingInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.1.length) ∧
    WeightedTardy i.1.1 order ≤ i.1.2 ∧ i.2.2 ≤ onTimeInS i.1.1 i.2.1 order

open Classical in
/-- CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT as a decision problem over
bitstrings. -/
noncomputable def constrainedSequencingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConstrainedSequencingInstance) x with
  | some i => decide (WellFormed i ∧ ConstrainedSequencingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
