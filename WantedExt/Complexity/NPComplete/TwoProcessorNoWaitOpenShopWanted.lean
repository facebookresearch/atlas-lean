/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
comment on p. 242 ("The analogous "no-wait" versions of OPEN-SHOP SCHEDULING and JOB-SHOP
SCHEDULING are NP-complete in the strong sense for m = 2 [Sahni and Cho, 1977b]");
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShop

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-!
# TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING is NP-complete

INSTANCE: `m = 2` processors, a set `J` of jobs, each job `j ∈ J` consisting of two tasks
`t₁[j], t₂[j]` (with `tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺` for each
such task `t`, and an overall deadline `D ∈ ℤ⁺`.
QUESTION: is there an open-shop schedule for `J` that meets the deadline and has no wait in
process, i.e. for each job `j` the two tasks run back to back in one of the two orders:
`σ₂(j) = σ₁(j) + l(t₁[j])` or `σ₁(j) = σ₂(j) + l(t₂[j])`?

This is the "no-wait" version of OPEN-SHOP SCHEDULING ([SS14], `OpenShopSchedulingWanted`) with
`m = 2`, which Garey and Johnson record in the comment to [SS16]. The no-wait condition of
[SS16], `σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`, fixes the processor order `1, 2`; in an open shop each job
chooses its own order, so the analogous condition is that some order of the job's tasks runs
without idle time between them, which for two processors is the disjunction above. The instance
type, `NoWaitFlowShopScheduling.WellFormed` and `NoWaitFlowShopScheduling.IsOpenShopSchedule`
(one-to-one one-processor schedules [SS1], disjoint task intervals per job, deadline) are the
parent's, unchanged; `WellFormed` adds `m = 2`. Sahni and Cho prove the two-processor problem
NP-hard even when no task has length zero; Garey and Johnson record it as NP-complete in the
strong sense. Membership in NP: the certificate is the start times, each at most `D`.
Processors are numbered `0, 1` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance with two
processors. -/
def WellFormed (i : OpenShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 2

/-- An open-shop schedule meeting the deadline in which every job runs its tasks back to back:
one task starts exactly when the job's task on the other processor ends. -/
def TwoProcessorNoWaitOpenShopFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsOpenShopSchedule i σ ∧
    ∀ j, ∃ p q : Fin i.1, p ≠ q ∧ σ q j = σ p j + taskLength i p j

open Classical in
/-- TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitOpenShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitOpenShopFeasible i)
  | none => false

/-- **TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson
(1979), [SS16]; Sahni and Cho (1979). -/
public theorem_wanted twoProcessorNoWaitOpenShop_npComplete :
    twoProcessorNoWaitOpenShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitOpenShopDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShop
