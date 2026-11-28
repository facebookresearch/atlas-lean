/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING with one-task jobs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
comment on p. 242 ("NP-complete in the strong sense for m = 2 if jobs with no tasks on the first
processor are allowed [Sahni and Cho, 1977b]");
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopOneTaskJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopOneTaskJobs

/-!
# TWO-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING with one-task jobs is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting either of two tasks
`t₁[j], t₂[j]` (with `tᵢ[j]` to be executed by processor `i`) or of the single task `t₂[j]` (no
task on the first processor), a length `l(t) ∈ ℤ₀⁺` for each such task `t`, and an overall
deadline `D ∈ ℤ⁺`.
QUESTION: is there a flow-shop schedule for `J` that meets the overall deadline and has the
property that `σ₂(j) = σ₁(j) + l(t₁[j])` for each job `j` with two tasks?

This is NO-WAIT FLOW-SHOP SCHEDULING ([SS16], `NoWaitFlowShopSchedulingWanted`) with `m = 2`,
extended, as in Garey and Johnson's comment, by jobs that have no task on the first processor.
Such a job is not a job with a first task of length zero: a one-processor schedule [SS1] is
one-to-one, so a zero-length first task still needs a start time of its own on processor 1, and
the second task must start at that time. The parent's instance type gives every job `m` tasks,
so this module has its own instance type and states the parent's schedule conditions directly:
`σ₁` (first tasks) and `σ₂` (second tasks, all jobs) are one-to-one one-processor schedules
(`σᵢ(j) > σᵢ(k)` implies `σᵢ(j) ≥ σᵢ(k) + l(tᵢ[k])`), every second task finishes by `D`, and a
job with two tasks starts its second task when its first task ends. The parent's remaining
conditions follow: the two task intervals of a job are disjoint and in flow-shop order, and a
first task ends at `σ₂(j) ≤ D`.

Garey and Johnson record the strong NP-completeness of this case, citing Sahni and Cho; their
paper's abstract states "The two processor flow shop problem is NP-Hard if jobs with only one
task are permitted", whereas with two tasks per job the problem is solvable in polynomial time
(Gilmore and Gomory 1964). Membership in NP: the certificate is the start times, each at most
`D`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING with one-task jobs is NP-complete.** Source:
Garey and Johnson (1979), [SS16]; Sahni and Cho (1979). -/
public theorem_wanted twoProcessorNoWaitFlowShopOneTaskJobs_npComplete :
    twoProcessorNoWaitFlowShopOneTaskJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitFlowShopOneTaskJobsDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopOneTaskJobs
