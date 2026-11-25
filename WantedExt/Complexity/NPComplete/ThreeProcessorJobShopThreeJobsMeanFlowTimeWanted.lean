/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs (J3|n=3|ΣC_i) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry `J3|n=3|ΣC_i`
(minimal NP-hard in the ordinary sense, citing Sotskov and Shakhlevich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsWanted
public import WantedExt.Complexity.NPComplete.TwoProcessorJobShopMeanFlowTimeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsMeanFlowTime

open JobShopScheduling (JobShopSchedulingInstance)

/-!
# THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs (J3|n=3|ΣC_i) is NP-complete

INSTANCE: a set `J` of `|J| = 3` jobs, each job `j ∈ J` consisting of an ordered collection of
tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and a
bound `K ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` on the `m = 3` processors whose
total completion time `∑_{j ∈ J} C_j` is at most `K`, `C_j = σ(t_{n_j}[j]) + l(t_{n_j}[j])`
being the time the last task of `j` finishes?

This is `J3|n=3|ΣC_i` in the Brucker-Knust classification. It combines two merged statements
over the [SS18] instance type `JobShopScheduling.JobShopSchedulingInstance`, whose last
component is read as the bound `K`:

* the instances are those of `ThreeProcessorJobShopThreeJobs.RestrictedWellFormed`
  (`J3|n=3|C_max`: a well-formed JOB-SHOP SCHEDULING instance, so `1 ≤ n_j` and `0 < K`, with
  `m = 3` and exactly three jobs);
* the question is `TwoProcessorJobShopMeanFlowTime.TwoProcessorJobShopMeanFlowTimeFeasible`
  (`J2||ΣC_i`: the job-shop schedule conditions with the bound `K` on `∑ C_j`). That
  predicate does not mention the number of processors (its `m = 2` is in its own
  `WellFormed`, not used here), so it states the total-completion-time question for every `m`.

The number `n_j` of tasks of a job is not bounded. Lengths and the bound use the canonical
binary encoding; Sotskov and Shakhlevich prove NP-hardness in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs, as a decision problem over
bitstrings. -/
noncomputable def threeProcessorJobShopThreeJobsMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (ThreeProcessorJobShopThreeJobs.RestrictedWellFormed i ∧
      TwoProcessorJobShopMeanFlowTime.TwoProcessorJobShopMeanFlowTimeFeasible i)
  | none => false

/-- **THREE-PROCESSOR JOB-SHOP MEAN FLOW TIME with three jobs (`J3|n=3|ΣC_i`) is
NP-complete.** Source: Sotskov and Shakhlevich (1995); Brucker and Knust's classification;
Garey and Johnson (1979), [SS18] (the parent problem). -/
public theorem_wanted threeProcessorJobShopThreeJobsMeanFlowTime_npComplete :
    threeProcessorJobShopThreeJobsMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorJobShopThreeJobsMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobsMeanFlowTime
