/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH RELEASE DATES, TOTAL COMPLETION TIME `P2|r_i|ΣC_i` is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|r_i|ΣC_i` (minimal NP-hard in the strong sense,
justified by the single-machine problem);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (`1|r_j|ΣC_j` is NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorReleaseTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorReleaseTotalCompletion

open TotalCompletionTimeWithReleaseTimes (TotalCompletionTimeWithReleaseTimesInstance Task
  taskLength releaseTime)

/-!
# TWO PARALLEL MACHINES WITH RELEASE DATES, TOTAL COMPLETION TIME `P2|r_i|ΣC_i` is NP-complete

INSTANCE: two identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with a processing time `p_i ∈ ℤ⁺` and a release date `r_i ∈ ℤ₀⁺` before
which it cannot start; and a positive integer `K`. QUESTION: is there a schedule, each job
processed without interruption on one of the machines, with total completion time
`∑_i C_i ≤ K`, where `C_i` is the completion time of job `i`?

Brucker and Knust record `P2|r_i|ΣC_i` as minimal NP-hard in the strong sense, justified by the
single-machine problem `1|r_i|ΣC_i`, which Lenstra, Rinnooy Kan and Brucker prove NP-hard in the
strong sense.

Encoding. The jobs and the bound are an instance of `1|r_j|ΣC_j`
(`TotalCompletionTimeWithReleaseTimesWanted`: one pair `(p_i, r_i)` per job, the jobs are
`Fin n`, and the bound `K`), whose well-formedness (positive processing times, `0 < K`) is
reused. A schedule gives each job a start time `σ(i) ≥ r_i` and a machine `μ(i) ∈ {0, 1}`; two
different jobs on the same machine occupy disjoint intervals. This is
`ParallelProcessorTotalFlowTimeWanted` with `m = 2` and the bound on `∑_i C_i` in place of the
bound on `∑_i (C_i - r_i)`. With integer data, integer start times lose no generality.
Membership in NP is the certificate argument: in a yes-instance every start time is below `K`,
and the start times and machines are checked in polynomial time. Binary encoding of all numbers
(the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO PARALLEL MACHINES WITH RELEASE DATES, TOTAL COMPLETION TIME `P2|r_i|ΣC_i` is
NP-complete.** Source: Brucker and Knust, *Complexity results for scheduling problems*; Lenstra,
Rinnooy Kan and Brucker (1977) for `1|r_j|ΣC_j`. -/
public theorem_wanted twoProcessorReleaseTotalCompletion_npComplete :
    twoProcessorReleaseTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorReleaseTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorReleaseTotalCompletion
