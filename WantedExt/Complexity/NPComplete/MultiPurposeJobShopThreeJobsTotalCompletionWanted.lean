/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|n=3|ΣC_i is NP-complete

Source:
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM3|n=3|ΣC_i`, minimal NP-hard in the ordinary sense, Sotskov and Shakhlevich
(1995));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsTotalCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM3|n=3|ΣC_i is NP-complete

INSTANCE: `m = 3` machines `M₁, M₂, M₃`; exactly `n = 3` jobs, each a chain of `n_j ≥ 1`
operations `O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a processing time
`p_{jk} ∈ ℤ₀⁺` and a nonempty set `μ_{jk} ⊆ {M₁, M₂, M₃}` of eligible machines and is processed
on exactly one machine of `μ_{jk}`; and a bound `K ∈ ℤ₀⁺`. Each machine processes at most one
operation at a time, and `O_{j,k+1}` cannot start before `O_{jk}` is completed. QUESTION: is there
a schedule whose total completion time `Σ_j C_j` is at most `K`, where `C_j` is the completion
time of job `j` (of its last operation)?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10, as stated in
`MultiPurposeJobShopThreeJobsWanted` (instance, operations, eligible machine sets, schedules and
`MPMWellFormed` are reused from there; the last component `K` of the instance is the bound on
the total completion time), with `m = 3` machines, exactly three jobs, and the total completion
time criterion. Brucker and Knust's classification lists `JMPM3|n=3|ΣC_i` as minimal NP-hard in
the ordinary sense, citing Sotskov and Shakhlevich (1995), who prove `J3|n=3|ΣC_i` NP-hard; a
dedicated-machine job shop is the MPM job shop in which every `μ_{jk}` is a single machine, and
for positive processing times the two have the same schedules. For zero processing times the
merged dedicated-machine statement `ThreeProcessorJobShopThreeJobsMeanFlowTimeWanted` also keeps
zero-length tasks on one processor at distinct start times, which this model (like
`MultiPurposeJobShopThreeJobsWanted`) does not: here an operation of length `0` occupies no
machine time, as in the classical scheduling model. The two formal languages therefore agree on
instances with positive processing times only, and neither is claimed to contain the other. The
model puts no condition on the machine sets of consecutive operations of a job.

Start times are natural numbers, which does not change the answer (see
`MultiPurposeJobShopThreeJobsWanted`). The number of machines is part of the instance, and
`WellFormed` fixes it to `3` and the number of jobs to `3`. Numbers use the binary encoding (the
problem is NP-hard in the ordinary sense only).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 3` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2, 3}`) and
exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 3 i ∧ i.2.1.length = 3

/-- Some MPM job shop schedule has `Σ_j C_j ≤ K`, where `C j` is the completion time of the last
operation of job `j`. -/
def MultiPurposeJobShopThreeJobsTotalCompletionFeasible (i : MPMJobShopInstance) :
    Prop :=
  ∃ a σ : Operation i → ℕ, IsMPMJobShopSchedule i a σ ∧
    ∃ C : Fin i.2.1.length → ℕ,
      (∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i ⟨j, k⟩) ∧
      ∑ j : Fin i.2.1.length, C j ≤ i.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|n=3|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multiPurposeJobShopThreeJobsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i =>
      decide (WellFormed i ∧ MultiPurposeJobShopThreeJobsTotalCompletionFeasible i)
  | none => false

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM3|n=3|ΣC_i` is NP-complete.** Source: Sotskov and
Shakhlevich (1995); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeJobShopThreeJobsTotalCompletion_npComplete :
    multiPurposeJobShopThreeJobsTotalCompletionDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            multiPurposeJobShopThreeJobsTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsTotalCompletion
