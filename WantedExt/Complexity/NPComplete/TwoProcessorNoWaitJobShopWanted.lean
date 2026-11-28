/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT JOB-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "The analogous 'no-wait' versions of OPEN-SHOP SCHEDULING and JOB-SHOP
SCHEDULING are NP-complete in the strong sense for `m = 2`"), with JOB-SHOP SCHEDULING [SS18];
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShopDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShop

/-!
# TWO-PROCESSOR NO-WAIT JOB-SHOP SCHEDULING is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of an ordered
collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a
processor `p(t) ∈ {1, 2}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`,
and a deadline `D ∈ ℤ⁺`.
QUESTION: is there a job-shop schedule for `J` that meets the overall deadline and has no wait
in process, i.e. `σ(t_{k+1}[j]) = σ(t_k[j]) + l(t_k[j])` for all `j ∈ J` and `1 ≤ k < n_j`?

This is the "no-wait" version of JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingDefs`) with
`m = 2`, which Garey and Johnson record in the comment to [SS16]: the no-wait condition of
[SS16], `σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`, applied to consecutive tasks of a job. In the
Brucker-Knust notation it is `J2|no-wait|C_max` (the deadline `D` bounds the makespan). The
instance type, `JobShopScheduling.WellFormed`, `JobShopScheduling.Task`,
`JobShopScheduling.taskLength` and `JobShopScheduling.taskProcessor` are the parent's,
unchanged; `WellFormed` adds `m = 2`. The feasibility predicate is the parent's job-shop
schedule meeting the deadline (one-processor schedules [SS1], job order, deadline) plus the
no-wait equality. Sahni and Cho show the problem NP-hard even when no task has length zero.
Task positions are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR NO-WAIT JOB-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson
(1979), [SS16], comment, with [SS18]; Sahni and Cho (1979). -/
public theorem_wanted twoProcessorNoWaitJobShop_npComplete :
    twoProcessorNoWaitJobShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitJobShopDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitJobShop
