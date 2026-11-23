/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB-SHOP SCHEDULING with two processors and at most three tasks per job is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING, p. 242
(comment: "NP-complete (in the ordinary sense) if `m = 2` and `n_j ≤ 3` for all `j ∈ J`");
T. Gonzalez and S. Sahni, "Flowshop and jobshop schedules: complexity and approximation",
Operations Research 26 (1978), 36-52, doi:10.1287/opre.26.1.36.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks

/-!
# JOB-SHOP SCHEDULING with two processors and at most three tasks per job is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of `n_j ≤ 3` tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length
`l(t) ∈ ℤ₀⁺` and a processor `p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J`
and `1 ≤ k < n_j`, and a deadline `D ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J`
that meets the overall deadline?

This is the restriction of JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`) to `m = 2`
and `n_j ≤ 3` for all `j ∈ J`. The instance type, `JobShopScheduling.WellFormed` (which
includes `n_j ≥ 1`) and `JobShopScheduling.JobShopSchedulingFeasible` are the parent's,
unchanged; `WellFormed` adds `m = 2` and `n_j ≤ 3`. Garey and Johnson record NP-completeness
in the ordinary sense (the problem is NP-complete in the strong sense for `m = 2` without the
bound on `n_j`), so the binary encoding of the task lengths and the deadline matters.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (`0 < m`, `1 ≤ n_j`, processors in
`{1, …, m}`, consecutive tasks of a job on different processors, `0 < D`), `m = 2`, and every
job has at most three tasks. -/
def WellFormed (i : JobShopScheduling.JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 2 ∧ ∀ job ∈ i.2.1, job.length ≤ 3

open Classical in
/-- JOB-SHOP SCHEDULING with two processors and at most three tasks per job, as a decision
problem over bitstrings. -/
noncomputable def twoProcessorJobShopThreeTasksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopScheduling.JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ JobShopScheduling.JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING with two processors and at most three tasks per job is
NP-complete.** Source: Garey and Johnson (1979), [SS18], comment; Gonzalez and Sahni (1978). -/
public theorem_wanted twoProcessorJobShopThreeTasks_npComplete :
    twoProcessorJobShopThreeTasksDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorJobShopThreeTasksDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks
