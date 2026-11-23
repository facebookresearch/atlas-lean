/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP FMPT2|chains;p_ij=1|Σw_iC_i is NP-complete

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT2|chains;p_ij=1|Σw_iC_i` as minimal NP-hard in the strong sense, citing
Tanaev et al. (1994), and class "Flow-shop problems without preemption", which lists the special
case `F2|p_ij=1;chains|Σw_iC_i` as minimal NP-hard in the strong sense, citing Tanaev et al.
(1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsWeightedCompletionWanted
public import WantedExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanWanted
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsWeightedCompletion

open MPMOpenShopTwoMachinesUnitChainsWeightedCompletion
  (MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance)
open MPTFlowShopTwoMachinesUnitChainsLateJobs (WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTPrecedenceSchedule)

/-!
# MPT FLOW SHOP FMPT2|chains;p_ij=1|Σw_iC_i is NP-complete

INSTANCE: machines `M_1, M_2`; an MPT flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with unit processing times (`p_ij = 1`), where `O_ij` needs all machines
of `μ_j` simultaneously and `O_i,j+1` cannot start before `O_ij` is completed; precedence
constraints forming chains (every job has at most one immediate predecessor and at most one
immediate successor; if `i` precedes `k`, no operation of `k` starts before `J_i` is completed);
weights `w_i`; and a bound `K`. Each machine processes at most one operation at a time. QUESTION:
is there a feasible schedule with total weighted completion time `Σ_i w_i C_i ≤ K`, where `C_i` is
the completion time of job `i` (that of its last operation)?

The MPT flow shop is Brucker's (*Scheduling Algorithms*, Chapter 11): each job has exactly `r`
operations, the `j`-th operation of every job requires all machines of the same set `μ_j`, the
machine sets are different, and the operations of a job are processed in the order of the stages.
The instance is that of the two-machine MPM open shop `OMPM2|chains;p_ij=1|Σw_iC_i`
(`MPMOpenShopTwoMachinesUnitChainsWeightedCompletionWanted`), the instance type
`MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance` (the machine sets as lists of machine
indices `0, 1`, one weight per job, so `n` is the length of that list and all processing times are
`1`, the chain arcs, and `K`); its well-formedness is that of `FMPT2|chains;p_ij=1|ΣU_i`
(`MPTFlowShopTwoMachinesUnitChainsLateJobs.WellFormed`: at least one stage, machine indices below
`2`, pairwise different sets, and chain arcs on the jobs), on the same instance type. The schedule
predicate is `MultiprocessorTaskFlowShopPrecedenceMakespan.IsMPTPrecedenceSchedule` for the chain
arcs: unit operations `(j, s)` with start times `σ j s`, operation `(j, s + 1)` starting no earlier
than operation `(j, s)` is completed, two different operations whose machine sets share a machine
at different times, and, for an arc `(i, k)`, every operation of `k` starting no earlier than
`C_i`; `C_j` is `MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time
of a job's operations. A machine set may be empty, as `μ_j ⊆ {M_1, M_2}` allows and as in
`MultiprocessorTaskFlowShopPrecedenceMakespanWanted`; operations of such a stage conflict with no
operation. With unit operations and integer data, integer start times lose no generality.

The classical flow shop `F2|p_ij=1;chains|Σw_iC_i` (`UnitFlowShopChainsWeightedCompletionWanted`)
is the special case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. Brucker and Knust list both problems as
minimal NP-hard in the strong sense, crediting Tanaev, Sotskov and Strusevich (1994), whose full
text was not available. Binary encoding of all numbers. Membership in NP: the start times are a
certificate; removing a time slot in which no operation runs keeps every constraint and increases
no completion time, so some optimal schedule has all `r n` start times below `r n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPT flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
total weighted completion time `Σ_j w_j C_j ≤ K`. -/
def MPTFlowShopTwoMachinesUnitChainsWeightedCompletionFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ,
    IsMPTPrecedenceSchedule i.1 i.2.2.1 σ ∧
      ∑ j, i.2.1.get j * completionTime (fun _ _ => 1) σ j ≤ i.2.2.2

open Classical in
/-- `FMPT2|chains;p_ij=1|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def mptFlowShopTwoMachinesUnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MPTFlowShopTwoMachinesUnitChainsWeightedCompletionFeasible i)
  | none => false

/-- **MPT FLOW SHOP FMPT2|chains;p_ij=1|Σw_iC_i is NP-complete.** Source: Tanaev, Sotskov and
Strusevich (1994), as recorded in the Brucker-Knust classification (with the special case
`F2|p_ij=1;chains|Σw_iC_i`); Brucker (2007), Chapter 11 (model). -/
public theorem_wanted mptFlowShopTwoMachinesUnitChainsWeightedCompletion_npComplete :
    mptFlowShopTwoMachinesUnitChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mptFlowShopTwoMachinesUnitChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MPTFlowShopTwoMachinesUnitChainsWeightedCompletion
