/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP SCHEDULING with three jobs (J3|n=3|Cmax) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem);
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry `J3|n=3|C_max`
(minimal NP-hard in the ordinary sense, citing Sotskov and Shakhlevich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobs

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# THREE-PROCESSOR JOB-SHOP SCHEDULING with three jobs (J3|n=3|Cmax) is NP-complete

INSTANCE: a set `J` of `|J| = 3` jobs, each job `j ∈ J` consisting of an ordered collection of
tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length `l(t) ∈ ℤ₀⁺` and a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and a
deadline `D ∈ ℤ⁺`. QUESTION: is there a job-shop schedule for `J` on the `m = 3` processors
that meets the overall deadline `D`, i.e. whose makespan `max_j C_j` is at most `D`?

This is `J3|n=3|C_max` in the Brucker-Knust classification: the restriction of JOB-SHOP
SCHEDULING (`WantedExt.Complexity.NPComplete.JobShopSchedulingWanted`) to instances with `m = 3`
processors and exactly three jobs. The number `n_j` of tasks of a job is not bounded. The
instance type, its `WellFormed` and `JobShopSchedulingFeasible` are reused unchanged; the
restriction is added to well-formedness. Lengths and the deadline use the canonical binary
encoding; Sotskov and Shakhlevich prove NP-hardness in the ordinary sense.

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
SCHEDULING instance, `m = 3`, and there are exactly three jobs. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ i.2.1.length = 3

open Classical in
/-- THREE-PROCESSOR JOB-SHOP SCHEDULING with three jobs, as a decision problem over
bitstrings. -/
noncomputable def threeProcessorJobShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING remains NP-complete with `m = 3` processors and three jobs
(`J3|n=3|C_max`).** Source: Sotskov and Shakhlevich (1995); Brucker and Knust's
classification; Garey and Johnson (1979), [SS18] (the parent problem). -/
public theorem_wanted threeProcessorJobShopThreeJobs_npComplete :
    threeProcessorJobShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorJobShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopThreeJobs
