/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣU_i`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|ΣU_i`, minimal NP-hard in the strong sense,
by reduction from the single machine problem `1|chains;p_i=1|ΣU_i`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (`1|chains, p_j = 1|ΣU_j`; Garey and Johnson,
[SS2], comment).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TardyTasksUnitChainsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingLateJobs

open MetaMathlibExt.Complexity.NPComplete.TardyTasksUnitChains
  (TardyTasksUnitChainsInstance Task deadline Prec)

/-- An instance: an instance of SEQUENCING TO MINIMIZE TARDY TASKS with unit lengths and chains
(due dates, the pairs `(t, t')` with `t` preceding `t'`, the bound `K`) and the batch capacity
`b`. -/
abbrev ChainsUnitParallelBatchingLateJobsInstance := TardyTasksUnitChainsInstance × ℕ

/-- Well-formedness of an instance: it is well-formed for SEQUENCING TO MINIMIZE TARDY TASKS with
unit lengths and chains (positive due dates, `0 < K ≤ n`, a strict partial order consisting of
chains), and `0 < b < n`. -/
def WellFormed (i : ChainsUnitParallelBatchingLateJobsInstance) : Prop :=
  TardyTasksUnitChains.WellFormed i.1 ∧ 0 < i.2 ∧ i.2 < i.1.1.length

/-- Some batch schedule `σ` (batch start time of each job) puts at most `b` jobs in each batch,
obeys the precedence constraints and has at most `K` late jobs, those with `σ(t) + 1 > d(t)`. -/
def ChainsUnitParallelBatchingLateJobsFeasible
    (i : ChainsUnitParallelBatchingLateJobsInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ i.2) ∧
    (∀ t t', Prec i.1 t t' → σ t + 1 ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i.1 t < σ t + 1).card ≤ i.1.2.2

open Classical in
/-- `1|chains;p_i=1;p-batch;b<n|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def chainsUnitParallelBatchingLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsUnitParallelBatchingLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ ChainsUnitParallelBatchingLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingLateJobs
