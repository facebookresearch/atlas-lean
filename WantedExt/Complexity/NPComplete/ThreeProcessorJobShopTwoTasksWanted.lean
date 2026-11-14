/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP SCHEDULING with at most two tasks per job is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment: "NP-complete (in the ordinary sense) if ... `m = 3` and `n_j ≤ 2` for all
`j ∈ J`";
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

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopTwoTasks

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# THREE-PROCESSOR JOB-SHOP SCHEDULING with at most two tasks per job is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of an ordered collection of at most two
tasks `t_k[j]`, `1 ≤ k ≤ n_j ≤ 2`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_1[j]) ≠ p(t_2[j])` when `n_j = 2`, and a deadline `D ∈ ℤ⁺`.
QUESTION: is there a job-shop schedule for `J` on the `m = 3` processors that meets the
overall deadline `D`?

This is the restriction of JOB-SHOP SCHEDULING
(`WantedExt.Complexity.NPComplete.JobShopSchedulingWanted`) to instances with `m = 3`
processors and `n_j ≤ 2` tasks in every job. The instance type, its `WellFormed` and
`JobShopSchedulingFeasible` are reused unchanged; the restriction is added to
well-formedness. Lengths and the deadline use the canonical binary encoding; the problem is
NP-complete in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance of the restriction: the instance is a well-formed JOB-SHOP
SCHEDULING instance, `m = 3`, and every job has at most two tasks. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ ∀ job ∈ i.2.1, job.length ≤ 2

open Classical in
/-- THREE-PROCESSOR JOB-SHOP SCHEDULING with at most two tasks per job, as a decision
problem over bitstrings. -/
noncomputable def threeProcessorJobShopTwoTasksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING remains NP-complete with `m = 3` processors and at most two tasks
per job.** Source: Garey and Johnson (1979), [SS18], comment; Gonzalez and Sahni (1978). -/
public theorem_wanted threeProcessorJobShopTwoTasks_npComplete :
    threeProcessorJobShopTwoTasksDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorJobShopTwoTasksDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopTwoTasks
