/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|r_i;p_ij=1|Σw_iC_i is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8
(the dedicated case `J2|r_j, p_ij = 1|∑ w_j C_j`, recorded by Brucker and Knust as strongly
NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `mpt_shop` (shop problems with multiprocessor tasks), Universität Osnabrück, which lists
`JMPT2|r_i; p_ij = 1|∑ w_i C_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the multiprocessor-task model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopReleaseWeighted

open UnitMultiPurposeJobShopMakespan (UnitMultiPurposeJobShopInstance Operation)
open UnitMultiprocessorTaskJobShopMakespan (IsUnitMPTSchedule)

/-!
# MULTIPROCESSOR-TASK JOB SHOP JMPT2|r_i;p_ij=1|Σw_iC_i is NP-complete

INSTANCE: `m = 2` processors `M₁, M₂`; jobs `j`, each a chain of `n_j ≥ 1` multiprocessor tasks
`O_{j1}, …, O_{jn_j}` with unit processing times, where task `O_{jk}` requires simultaneously
all processors of a given nonempty set `μ_{jk} ⊆ {M₁, M₂}`; tasks requiring a common processor
cannot be processed simultaneously, and `O_{j,k+1}` cannot start before `O_{jk}` is completed;
for every job a release date `r_j ∈ ℤ₀⁺` and a weight `w_j ∈ ℤ₀⁺`; a bound `K`. QUESTION: is there
a schedule in which no job starts before its release date and whose total weighted completion
time `∑_j w_j C_j` is at most `K`, `C_j` being the completion time of the last task of `j`?

This is the multiprocessor-task job shop of Brucker (*Scheduling Algorithms*, Chapter 11: every
task occupies all processors of its set, tasks requiring a common processor are incompatible,
and every job is a chain of tasks) with release dates and weights. Brucker and Knust list
`JMPT2|r_i; p_ij = 1|∑ w_i C_i` as minimal NP-hard in the strong sense, citing Timkovsky (1998),
who proves the dedicated-processor case `J2|r_j, p_ij = 1|∑ w_j C_j` NP-hard in the strong sense:
that is the special case in which every task requires a single processor and consecutive tasks of
a job require different processors. Membership in NP: the start times are a certificate.

The instance, tasks, well-formedness and schedules are those of
`UnitMultiprocessorTaskJobShopMakespanWanted` (`JMPT2|p_ij = 1|C_max`): the instance
`UnitMultiPurposeJobShopInstance` (the number `m` of processors, the jobs as lists of their tasks,
each task given by the list of processors it requires, and in the last place the bound `K`), its
`WellFormed` (`m = 2`, every job has a task, every processor set is nonempty and lies in
`{1, 2}`) and `IsUnitMPTSchedule` (natural start times, tasks sharing a processor start at
different times, the tasks of a job in order). The release dates and weights are a list of pairs
`(r_j, w_j)`, one per job, in the order of the jobs. Binary encoding of all numbers (the problem
is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a `JMPT2|p_ij = 1|C_max` instance (`m`, the jobs, and the bound `K`, here on the
total weighted completion time) and the pairs `(r_j, w_j)` of release dates and weights, one per
job. -/
abbrev UnitMultiprocessorTaskJobShopReleaseWeightedInstance :=
  UnitMultiPurposeJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed `JMPT2|p_ij = 1|C_max` instance (`m = 2`,
every job nonempty, every processor set nonempty in `{1, 2}`), and one pair `(r_j, w_j)` per
job. -/
def WellFormed (i : UnitMultiprocessorTaskJobShopReleaseWeightedInstance) : Prop :=
  UnitMultiprocessorTaskJobShopMakespan.WellFormed i.1 ∧ i.2.length = i.1.2.1.length

/-- Some unit-time multiprocessor-task job-shop schedule starts the first task of every job no
earlier than its release date `r_j` and has `∑_j w_j C_j ≤ K`, where `C j` is the completion
time of the last task of job `j`. -/
def UnitMultiprocessorTaskJobShopReleaseWeightedFeasible
    (i : UnitMultiprocessorTaskJobShopReleaseWeightedInstance) : Prop :=
  ∃ σ : Operation i.1 → ℕ, IsUnitMPTSchedule i.1 σ ∧
    (∀ j (k : Fin (i.1.2.1.get j).length), k.1 = 0 → (i.2.getD j (0, 0)).1 ≤ σ ⟨j, k⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + 1) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * C j ≤ i.1.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP `JMPT2|r_i;p_ij=1|Σw_iC_i` as a decision problem over
bitstrings. -/
noncomputable def unitMultiprocessorTaskJobShopReleaseWeightedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitMultiprocessorTaskJobShopReleaseWeightedInstance) x with
  | some i => decide (WellFormed i ∧ UnitMultiprocessorTaskJobShopReleaseWeightedFeasible i)
  | none => false

/-- **MULTIPROCESSOR-TASK JOB SHOP `JMPT2|r_i;p_ij=1|Σw_iC_i` is NP-complete.** Source: Timkovsky
(1998); Brucker and Knust, scheduling classification, class `mpt_shop`; Brucker (2007),
Chapter 11. -/
public theorem_wanted unitMultiprocessorTaskJobShopReleaseWeighted_npComplete :
    unitMultiprocessorTaskJobShopReleaseWeightedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitMultiprocessorTaskJobShopReleaseWeightedDec

end MetaMathlibExt.Complexity.NPComplete.UnitMultiprocessorTaskJobShopReleaseWeighted
