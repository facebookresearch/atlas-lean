/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL BATCHING `1|chains;p_i=1;p-batch;b<n|ΣT_i`: definitions

Source:
P. Brucker, A. Gladky, H. Hoogeveen, M. Y. Kovalyov, C. N. Potts, T. Tautenhahn and
S. L. van de Velde, "Scheduling a batching machine", Journal of Scheduling 1 (1998), 31-54,
doi:10.1002/(SICI)1099-1425(199806)1:1<31::AID-JOS4>3.0.CO;2-R (the parallel batching model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel batching problems"
(`1|chains;p_i=1;p-batch;b<n|ΣT_i`, minimal NP-hard in the strong sense,
by reduction from the single machine problem `1|chains;p_i=1|ΣT_i`);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, p_j = 1|ΣT_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.ChainsUnitTaskTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingTotalTardiness

open MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness
  (PrecedenceUnitTaskTardinessInstance Prec)
open MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
  (Task taskLength weight deadline)

/-- An instance: an instance of `1|chains, p_j = 1|ΣT_j` (job triples `(l(t), w(t), d(t))`, the
bound `K`, the pairs `(t, t')` with `t` preceding `t'`) and the batch capacity `b`. -/
abbrev ChainsUnitParallelBatchingTotalTardinessInstance :=
  PrecedenceUnitTaskTardinessInstance × ℕ

/-- Well-formedness of an instance: it is well-formed for `1|chains, p_j = 1|ΣT_j` (unit lengths
and weights, positive due dates and `K`, a chain-like strict partial order), and `0 < b < n`. -/
def WellFormed (i : ChainsUnitParallelBatchingTotalTardinessInstance) : Prop :=
  ChainsUnitTaskTardiness.WellFormed i.1 ∧ 0 < i.2 ∧ i.2 < i.1.1.1.length

/-- Some batch schedule `σ` (batch start time of each job) puts at most `b` jobs in each batch,
obeys the precedence constraints and has total tardiness at most `K`: the sum, over the jobs
with `σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)`. -/
def ChainsUnitParallelBatchingTotalTardinessFeasible
    (i : ChainsUnitParallelBatchingTotalTardinessInstance) : Prop :=
  ∃ σ : Task i.1.1 → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ i.2) ∧
    (∀ t t', Prec i.1 t t' → σ t + taskLength i.1.1 t ≤ σ t') ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i.1.1 t < σ t + taskLength i.1.1 t),
      (σ t + taskLength i.1.1 t - deadline i.1.1 t) * weight i.1.1 t ≤ i.1.1.2

open Classical in
/-- `1|chains;p_i=1;p-batch;b<n|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def chainsUnitParallelBatchingTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsUnitParallelBatchingTotalTardinessInstance) x with
  | some i => decide (WellFormed i ∧ ChainsUnitParallelBatchingTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitParallelBatchingTotalTardiness
