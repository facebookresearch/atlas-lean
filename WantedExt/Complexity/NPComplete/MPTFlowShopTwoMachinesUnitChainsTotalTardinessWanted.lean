/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP FMPT2|chains;p_ij=1|ΣT_i is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT2|chains;p_ij=1|ΣT_i` as minimal NP-hard in the strong sense
("Single-machine problem");
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with precedence
constraints", ORSA Journal on Computing 2 (1990), 346-352, doi:10.1287/ijoc.2.4.346 (the
single-machine problem `1|chains;p_j=1|ΣT_j`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsTotalTardiness

open MPMOpenShopTwoMachinesUnitChainsLateJobs (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance)
open MPTFlowShopTwoMachinesUnitChainsLateJobs (WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-!
# MPT FLOW SHOP FMPT2|chains;p_ij=1|ΣT_i is NP-complete

INSTANCE: machines `M_1, M_2`; an MPT flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with unit processing times (`p_ij = 1`), where `O_ij` requires every
machine of `μ_j` during its processing and `O_i,j+1` cannot start before `O_ij` is completed;
precedence constraints forming chains (every job has at most one immediate predecessor and at most
one immediate successor; if `i` precedes `k`, no operation of `k` starts before `J_i` is completed);
due dates `d_i`; and a bound `K`. Operations requiring a common machine cannot be processed
simultaneously. QUESTION: is there a feasible schedule with total tardiness `Σ_i T_i ≤ K`, where
`T_i = max(0, C_i - d_i)` and `C_i` is the completion time of job `i` (that of its last operation)?

The MPT flow shop is Brucker's (*Scheduling Algorithms*, Chapter 11), as in
`MultiprocessorTaskFlowShopPrecedenceMakespanWanted` (`FMPT|prec;p_ij=1|C_max`): every job has the
same number `r` of operations (stages), the operation of stage `j` occupies every machine of the set
`μ_j` while it is processed, the sets `μ_j` are pairwise different, and operations needing a common
machine cannot run at the same time. The instance and its well-formedness are those of
`FMPT2|chains;p_ij=1|ΣU_i` (`MPTFlowShopTwoMachinesUnitChainsLateJobsWanted`): the instance shape
`MPMOpenShopTwoMachinesUnitChainsLateJobs.MPMOpenShopTwoMachinesUnitChainsLateJobsInstance` (the
machine sets as lists of machine indices `0, 1`, one due date per job, so `n` is the length of that
list and all processing times are `1`, the chain arcs, and `K`) and
`MPTFlowShopTwoMachinesUnitChainsLateJobs.WellFormed` (at least one stage, machine indices below
`2`, pairwise different sets, and chain arcs on the jobs). The schedule predicate is
`MultiprocessorTaskFlowShopPrecedenceMakespan.IsMPTPrecedenceSchedule` for the chain arcs: unit
operations `(j, s)` with start times `σ j s`, operation `(j, s + 1)` starting no earlier than
operation `(j, s)` is completed, two different operations whose machine sets share a machine at
different times, and, for an arc `(i, k)`, every operation of `k` starting no earlier than `C_i`;
`C_j` is `MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a
job's operations. A machine set may be empty, as `μ_j ⊆ {M_1, M_2}` allows and as in
`MultiprocessorTaskFlowShopPrecedenceMakespanWanted`; operations of such a stage conflict with no
operation. With unit operations and integer data, integer start times lose no generality.

The single-machine problem `1|chains;p_i=1|ΣT_i` (`ChainsUnitTaskTardinessWanted`), strongly NP-hard
by Leung and Young (1990), is the special case `r = 1`, `μ_1 = {M_1}`; Brucker and Knust list
`FMPT2|chains;p_ij=1|ΣT_i` as minimal NP-hard in the strong sense on that basis ("Single-machine
problem"). Binary encoding of all numbers. Membership in NP: the start times are a certificate;
removing a time slot in which no operation runs keeps every constraint and increases no completion
time, so some optimal schedule has all `r n` start times below `r n`.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPT flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
total tardiness `Σ_j max(0, C_j - d_j)` at most `K` (natural-number subtraction truncates at `0`).
-/
def MPTFlowShopTwoMachinesUnitChainsTotalTardinessFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ,
    IsMPTPrecedenceSchedule i.1 i.2.2.1 σ ∧
      (∑ j, (completionTime (fun _ _ => 1) σ j - i.2.1.get j)) ≤ i.2.2.2

open Classical in
/-- `FMPT2|chains;p_ij=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def mptFlowShopTwoMachinesUnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPTFlowShopTwoMachinesUnitChainsTotalTardinessFeasible i)
  | none => false

/-- **MPT FLOW SHOP FMPT2|chains;p_ij=1|ΣT_i is NP-complete.** Source: Brucker and Knust's
classification ("Single-machine problem": Leung and Young (1990), `1|chains;p_i=1|ΣT_i`); Brucker
(2007), Chapter 11 (model). -/
public theorem_wanted mptFlowShopTwoMachinesUnitChainsTotalTardiness_npComplete :
    mptFlowShopTwoMachinesUnitChainsTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mptFlowShopTwoMachinesUnitChainsTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsTotalTardiness
