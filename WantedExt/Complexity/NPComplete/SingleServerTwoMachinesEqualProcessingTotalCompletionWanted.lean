/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, total completion time
(`P2;S1|p_i=p|ΣC_i`) is NP-complete

Source:
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|p_i=p|ΣC_i`, minimal NP-hard,
citing Brucker et al. 2002).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualProcessingTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualProcessingTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (IsSingleServerSchedule)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, total completion time, is
NP-complete

INSTANCE: `m = 2` identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with a setup time `s_i ∈ ℤ₀⁺`; a processing time `p ∈ ℤ⁺`, the same for all
jobs (`p_i = p`); and a bound `K`. Each job is processed on one machine, without interruption.
Immediately before its processing, job `i` must be loaded (set up) on its machine, which takes
the setup time `s_i`; during the setup both the machine and the server are occupied, and all
setups are done by a single server, which handles at most one job at a time. QUESTION: is there
a feasible schedule whose total completion time `Σ_i C_i` is at most `K`, where `C_i` is the
completion time of job `i`?

This is `P2;S1|p_i=p|ΣC_i` in the notation of Brucker et al. and the Brucker-Knust
classification. Jobs are listed one per entry, by their setup times; jobs are `Fin n`. A
schedule is a `SingleServerTwoMachinesEqualSetupMakespan.IsSingleServerSchedule` on two machines
with setup times `s_j` and processing time `p` for every job: job `j` is set up on machine `μ j`
during `[t j, t j + s_j)` and processed there until `C_j = t j + s_j + p`. Start times are
natural numbers as in that module (rounding all start times down keeps a schedule feasible and
increases no completion time). Membership in NP is the certificate argument: the machine and the
setup start time (at most `K`) of every job, checked pairwise in polynomial time. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, total completion time
(`P2;S1|p_i=p|ΣC_i`) is NP-complete.** Source: Brucker, Dhaenens-Flipo, Knust, Kravchenko and
Werner (2002), as recorded in the Brucker-Knust classification. -/
public theorem_wanted singleServerTwoMachinesEqualProcessingTotalCompletion_npComplete :
    singleServerTwoMachinesEqualProcessingTotalCompletionDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            singleServerTwoMachinesEqualProcessingTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualProcessingTotalCompletion
