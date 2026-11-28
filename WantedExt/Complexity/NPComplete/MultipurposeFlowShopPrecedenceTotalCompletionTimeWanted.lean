/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, PRECEDENCE, TOTAL COMPLETION TIME (FMPM|prec; p_ij = 1|ΣC_i) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Section 1.3 (precedence
relations), Chapter 10 (the MPM flow-shop model) and Table 5.3 (`P|p_i = 1; prec|ΣC_i` is
NP-hard, Lenstra and Rinnooy Kan);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|prec; p_ij = 1|ΣC_i` as strongly NP-hard with the attribution to
Lenstra and Rinnooy Kan (1978).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceTotalCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceTotalCompletionTime

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed PrecedenceWellFormed
  IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP, PRECEDENCE, TOTAL COMPLETION TIME (FMPM|prec; p_ij = 1|ΣC_i) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`; a precedence relation `→` on the
jobs given by an acyclic digraph; and a bound `K`. QUESTION: is there a feasible schedule with
total completion time `Σ_i C_i ≤ K`?

The MPM flow-shop model, its schedules and precedence constraints are those of
`FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's model: `StagesWellFormed`, `PrecedenceWellFormed`, `IsPrecedenceSchedule`,
`completionTime`, reused here); only the objective differs. As there, the acyclic precedence
digraph is given by its transitive closure, the list of all pairs `(i, k)` with `i → k`, required
to be a strict partial order (`PrecedenceWellFormed`: Mathlib's `IsStrictOrder`); a digraph and its
closure admit the same schedules, since along `i → c → k` we get `C_i ≤ S_c < C_c ≤ S_k`. The
jobs are listed explicitly, one list `[p_i1, …, p_ir]` of processing times per job, each required
to be `1` (the convention of `PrecedenceConstrainedSchedulingWanted`, which lists unit task
lengths), so the input length grows with the number of jobs. Every stage machine set must be
nonempty: an operation "has to be processed by one machine in the set" (Brucker, Chapter 10).
Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`FMPM|prec; p_ij = 1|ΣC_i` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Lenstra and Rinnooy Kan (1978); Brucker and Knust, *Complexity results for scheduling
problems*. -/
public theorem_wanted multipurposeFlowShopPrecedenceTotalCompletionTime_npComplete :
    multipurposeFlowShopPrecedenceTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopPrecedenceTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceTotalCompletionTime
