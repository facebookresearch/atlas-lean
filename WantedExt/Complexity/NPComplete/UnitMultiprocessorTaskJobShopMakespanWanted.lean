/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|p_ij=1|Cmax is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model) and Section 11.2, "Job Shop Problems" (records that
`JMPT2|p_ij = 1|C_max` is NP-hard, credited to Brucker and Krämer);
P. Brucker and A. Krämer, "Shop scheduling problems with multiprocessor tasks on dedicated
processors", Annals of Operations Research 57 (1995), 13-27, doi:10.1007/BF02099688 (not
available; Brucker's book records the result and its attribution);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|p_ij = 1|C_max` as minimal NP-hard in the strong sense, citing Brucker and Krämer (1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitMultiPurposeJobShopMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespan

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation eligible
  IsMPMInstance)

/-!
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|p_ij=1|Cmax is NP-complete

INSTANCE: `m = 2` processors `M₁, M₂`; jobs, each a chain of `n_j ≥ 1` multiprocessor tasks
`O_{j1}, …, O_{jn_j}` with unit processing times, where task `O_{jk}` requires simultaneously
all processors of a given nonempty set `μ_{jk} ⊆ {M₁, M₂}` during its processing; tasks
requiring a common processor cannot be processed simultaneously, and `O_{j,k+1}` cannot start
before `O_{jk}` is completed; a bound `K`. QUESTION: is there a schedule whose makespan, the
largest completion time of a task, is at most `K`?

The multiprocessor-task (MPT) model is Brucker's (*Scheduling Algorithms*, Chapter 11): "Each
task `i` requires during a processing period `p_i` all processors belonging to a subset
`µ_i ⊆ {M_1, …, M_m}`. Tasks requiring the same processor cannot be processed simultaneously.
[...] The multiprocessor task job shop problem is a special case of the general shop problem
with MPT in which each job consists of a chain of tasks." Brucker's Section 11.2 states:
"Problem `JMPT2 | p_ij = 1 | C_max` is NP-hard (Brucker & Krämer), contrary to the fact that
`J2 | p_ij = 1 | C_max` is polynomially solvable"; Brucker and Knust list it as minimal NP-hard
in the strong sense. With two processors a task requires `{M₁}`, `{M₂}` or both (Brucker's
Section 11.1: "bi-processor tasks and two types of single-processor tasks"); the model puts no
condition on the sets of consecutive tasks of a job. Membership in NP: the start times are a
certificate.

The instance has the shape of the unit-time multi-purpose job shop of
`UnitMultiPurposeJobShopMakespanWanted`, which is reused: `UnitMultiPurposeJobShopInstance` (the
number `m` of processors, the jobs as lists of their tasks in order, each task given by a list of
processors numbered `1, …, m`, and the bound `K`), its tasks `Operation`, the listed set
`eligible i t`, which is here the set `μ_{jk}` of processors the task requires, and
`IsMPMInstance` (every job has a task, every set is nonempty, every processor lies in
`{1, …, m}`). A schedule gives every task `t` a start time `σ t ∈ ℤ₀⁺`, so `t` occupies
`[σ t, σ t + 1)` on every processor of its set: two different tasks whose sets share a processor
start at different times, and every task of a job starts after the previous task of the job is
completed. Natural start times lose no generality: rounding every start time of a feasible
schedule down keeps it feasible and does not increase completion times. Binary encoding of all
numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A schedule of the unit-time multiprocessor-task job shop: start times `σ` such that two
different tasks whose processor sets share a processor start at different times (with unit
processing times, they do not overlap), and every task of a job starts after the previous task
of the job completes. -/
def IsUnitMPTSchedule (i : UnitMultiPurposeJobShopInstance) (σ : Operation i → ℕ) : Prop :=
  (∀ t t', t ≠ t' → (∃ M, M ∈ eligible i t ∧ M ∈ eligible i t') → σ t ≠ σ t') ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 → σ ⟨j, k⟩ + 1 ≤ σ ⟨j, k'⟩

/-- Well-formedness of an instance: `m = 2`, and the instance describes a job shop whose tasks
have nonempty processor sets in `{1, …, m}` (`IsMPMInstance`). -/
def WellFormed (i : UnitMultiPurposeJobShopInstance) : Prop :=
  i.1 = 2 ∧ IsMPMInstance i

/-- Some schedule completes every task by `K`: the last task of every job, which completes after
the job's other tasks, ends by `K`. -/
def UnitMultiprocessorTaskJobShopMakespanFeasible (i : UnitMultiPurposeJobShopInstance) :
    Prop :=
  ∃ σ : Operation i → ℕ, IsUnitMPTSchedule i σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length → σ ⟨j, k⟩ + 1 ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP `JMPT2|p_ij=1|C_max` as a decision problem over bitstrings. -/
noncomputable def unitMultiprocessorTaskJobShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiPurposeJobShopInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiprocessorTaskJobShopMakespanFeasible i)
  | none => false

/-- **MULTIPROCESSOR-TASK JOB SHOP `JMPT2|p_ij=1|C_max` is NP-complete.** Source: Brucker (2007),
Section 11.2; Brucker and Krämer (1995); Brucker and Knust, scheduling classification, class
`mpt_shop`. -/
public theorem_wanted unitMultiprocessorTaskJobShopMakespan_npComplete :
    unitMultiprocessorTaskJobShopMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitMultiprocessorTaskJobShopMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespan
