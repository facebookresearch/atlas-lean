/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT job-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", entry `JMPT3|n=3|ΣC_i` (minimal NP-hard in the ordinary sense, citing Sotskov and
Shakhlevich 1995);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|ΣC_i` is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength)
open MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobs
  (WellFormed IsMPTJobShopSchedule)

/-!
# MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i is NP-complete

INSTANCE: machines `M_1, M_2, M_3`; exactly three jobs, job `j` a chain of tasks
`O_j1, …, O_jn_j`, where task `O_jk` has a processing time `p_jk ∈ ℕ` and a nonempty set
`μ_jk ⊆ {M_1, M_2, M_3}` of machines, all of which it occupies simultaneously during its
processing, and `O_j,k+1` cannot start before `O_jk` is completed; tasks whose machine sets
intersect cannot be processed at the same time; and a bound `K`. QUESTION: is there a feasible
schedule whose total completion time `∑_j C_j` is at most `K`, where `C_j` is the completion time
of job `j` (that of its last task)?

Brucker and Knust list `JMPT3|n=3|ΣC_i` as minimal NP-hard in the ordinary sense, citing Sotskov
and Shakhlevich, who prove `J3|n=3|ΣC_i` NP-hard: a classical job-shop task on machine `M` is the
multiprocessor task with `μ_jk = {M}`. The instances, their well-formedness and the schedules are
those of `MultiprocessorTaskJobShopThreeJobsWanted` (`JMPT3|n=3|C_max`:
`MultiprocessorTaskJobShopThreeJobs.WellFormed` and
`MultiprocessorTaskJobShopThreeJobs.IsMPTJobShopSchedule`, over the instance data of
`MultiPurposeJobShopThreeJobsWanted`), with the last component of the instance read as the bound
`K` on `∑_j C_j`. The values `C j` bound the completion time of the last task of each job `j`;
the least such values are the completion times, so some choice has sum at most `K` exactly when
`∑_j C_j ≤ K`. Lengths and the bound use the canonical binary encoding. Membership in NP: some
optimal schedule has start times that are sums of processing times, a certificate of polynomial
size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPT job shop schedule has total completion time at most `K`: values `C j`, each at
least the completion time of the last task of job `j`, sum to at most `K`. -/
def MultiprocessorTaskJobShopThreeJobsTotalCompletionFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ (σ : Operation i → ℕ) (C : Fin i.2.1.length → ℕ), IsMPTJobShopSchedule i σ ∧
    (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ C j) ∧ ∑ j, C j ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskJobShopThreeJobsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskJobShopThreeJobsTotalCompletionFeasible i)
  | none => false

/-- **MULTIPROCESSOR-TASK JOB SHOP JMPT3|n=3|ΣC_i is NP-complete.** Source: Brucker and Knust's
classification, citing Sotskov and Shakhlevich (1995); Brucker (2004), Chapter 11 (the model). -/
public theorem_wanted multiprocessorTaskJobShopThreeJobsTotalCompletion_npComplete :
    multiprocessorTaskJobShopThreeJobsTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskJobShopThreeJobsTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskJobShopThreeJobsTotalCompletion
