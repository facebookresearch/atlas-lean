/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING (J3|p_ij=1;no-wait|Cmax) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem) and problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING (the no-wait condition
`σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`);
C. Sriskandarajah and P. Ladet, "Some no-wait shops scheduling problems: complexity aspect",
European Journal of Operational Research 24 (1986), 424-438,
doi:10.1016/0377-2217(86)90036-6;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_now`, entry
`J3|p_ij=1;no-wait|C_max` (minimal NP-hard in the strong sense, citing Sriskandarajah and
Ladet 1986).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShopDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShop

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-!
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING (J3|p_ij=1;no-wait|Cmax) is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of an ordered collection of tasks
`t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1`, for each task `t` a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and a
deadline `D ∈ ℤ⁺`. QUESTION: is there a no-wait job-shop schedule for `J` on the `m = 3`
processors that meets the overall deadline `D`, i.e. a job-shop schedule in which
`σ(t_{k+1}[j]) = σ(t_k[j]) + l(t_k[j])` for all `j ∈ J` and `1 ≤ k < n_j` (each task of a job
starts exactly when the previous one finishes) and whose makespan `max_j C_j` is at most `D`?

This is `J3|p_ij=1;no-wait|C_max` in the Brucker-Knust classification. The instance type
`JobShopScheduling.JobShopSchedulingInstance`, its tasks, lengths and processors, and the
well-formedness of THREE-PROCESSOR JOB-SHOP SCHEDULING with equal task lengths
(`ThreeProcessorEqualLengthJobShop.RestrictedWellFormed`: a well-formed [SS18] instance with
`m = 3` whose tasks all have one length) are reused; unit lengths are added to
well-formedness. The schedule conditions are those of `JobShopScheduling.JobShopSchedulingFeasible`
(start times one-to-one on the tasks of each processor, one task at a time on each processor,
every job finished by `D`), with the condition that each task of a job starts no earlier than
the previous one finishes replaced by the no-wait equality, as [SS16] does for flow shops.
Task positions are numbered from `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING (`J3|p_ij=1;no-wait|C_max`) is
NP-complete.** Source: Sriskandarajah and Ladet (1986); Brucker and Knust's classification;
Garey and Johnson (1979), [SS18] and [SS16] (the parent problem and the no-wait condition). -/
public theorem_wanted threeProcessorUnitNoWaitJobShop_npComplete :
    threeProcessorUnitNoWaitJobShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorUnitNoWaitJobShopDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShop
