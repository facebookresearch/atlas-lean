/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O2|no-wait|ΣC_i is NP-complete

Source:
W. Kubiak, C. Sriskandarajah and K. Zaras, "A note on the complexity of openshop scheduling
problems", INFOR 29 (1991), 284-294, doi:10.1080/03155986.1991.11732176 (abstract: "The problem
of minimizing mean flow time in no-wait openshop ... [is] shown to be NP-hard"; the full text was
not available); recorded as strongly NP-hard (a minimal NP-hard problem) in P. Brucker and
S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems with nowait"
(University of Osnabrück, http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem
`O2|no-wait|ΣC_i`, credited to Kubiak et al. (1991).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShopTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShopTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-!
# NO-WAIT OPEN SHOP O2|no-wait|ΣC_i is NP-complete

INSTANCE: an open shop with two machines `M_1, M_2` and jobs `1, …, n`; job `i` consists of two
operations `O_i1, O_i2` with processing times `p_i1, p_i2 ∈ ℤ₀⁺`, `O_ij` processed on `M_j`, in
either order but not at the same time; each machine processes at most one operation at a time;
no wait: the second operation of a job starts exactly when its first operation is completed; a
bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule whose total completion time `Σ_i C_i` is at most
`K`, where `C_i` is the completion time of job `i` (of its last operation)?

This is Brucker and Knust's `O2|no-wait|ΣC_i`, listed as minimal strongly NP-hard and credited
to Kubiak, Sriskandarajah and Zaras (1991), and the total-completion-time version of
TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING (`TwoProcessorNoWaitOpenShopWanted`), whose makespan
version is `O2|no-wait|C_max`. The instance is an OPEN-SHOP SCHEDULING instance of
`OpenShopSchedulingInstance` (the number `m` of machines, the jobs, each listed as the list
`[p_i1, p_i2]` of its task lengths, and a bound, here `K`). The schedule is
`NoWaitFlowShopScheduling.IsOpenShopSchedule` (each machine's start times are pairwise distinct
and a later task starts after an earlier one completes, the tasks of a job occupy disjoint
intervals, and every task completes by the bound `K`), with the no-wait condition of
`TwoProcessorNoWaitOpenShopWanted` (one task of each job starts when the job's other task ends).
The parent's clause that every task completes by `K` follows from `Σ_i C_i ≤ K`, so it does not
restrict the problem. `C_i` is the largest completion time of a task of job `i`. `WellFormed`
requires `m = 2` and two tasks per job; unlike the parent's deadline, `K = 0` is allowed. Binary
encoding of all numbers. Membership in NP: the start times are a certificate, each below `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NO-WAIT OPEN SHOP `O2|no-wait|ΣC_i` is NP-complete.** Source: Kubiak, Sriskandarajah and
Zaras (1991), as recorded in the Brucker-Knust classification of scheduling problems. -/
public theorem_wanted twoProcessorNoWaitOpenShopTotalCompletion_npComplete :
    twoProcessorNoWaitOpenShopTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitOpenShopTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShopTotalCompletion
