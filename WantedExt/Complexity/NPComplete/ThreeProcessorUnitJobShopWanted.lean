/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME JOB-SHOP SCHEDULING (J3|p_ij=1|Cmax) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment: "If in the nonpreemptive case all tasks have the same length, the problem
is NP-complete for `m = 3`";
J. K. Lenstra and A. H. G. Rinnooy Kan, "Computational complexity of discrete optimization
problems", Annals of Discrete Mathematics 4 (1979), 121-140,
doi:10.1016/S0167-5060(08)70821-5 (cited by Garey and Johnson as [Lenstra and Rinnooy Kan,
1978b]);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop`, entry
`J3|p_ij=1|C_max` (minimal NP-hard in the strong sense, citing Lenstra and Rinnooy Kan 1979).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShopWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitJobShop

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# THREE-PROCESSOR UNIT-TIME JOB-SHOP SCHEDULING (J3|p_ij=1|Cmax) is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of an ordered collection of tasks
`t_k[j]`, `1 ≤ k ≤ n_j`, each of length `l(t) = 1`, for each task `t` a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and a
deadline `D ∈ ℤ⁺`. QUESTION: is there a (nonpreemptive) job-shop schedule for `J` on the
`m = 3` processors that meets the overall deadline `D`, i.e. whose makespan `max_j C_j` is at
most `D`?

This is `J3|p_ij=1|C_max` in the Brucker-Knust classification, the problem Lenstra and
Rinnooy Kan prove NP-complete: the restriction of THREE-PROCESSOR JOB-SHOP SCHEDULING with
equal task lengths (`WantedExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShopWanted`),
whose common length is part of the instance, to the common length `1`. The instance type,
JOB-SHOP SCHEDULING's `JobShopSchedulingFeasible` and the equal-length restriction's
`RestrictedWellFormed` (`m = 3`, all tasks of one length) are reused unchanged; unit lengths
are added to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance of the restriction: the instance is a well-formed
THREE-PROCESSOR JOB-SHOP SCHEDULING instance with equal task lengths (a well-formed JOB-SHOP
SCHEDULING instance with `m = 3` whose tasks all have one length), and every task has length
`1`. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  ThreeProcessorEqualLengthJobShop.RestrictedWellFormed i ∧ ∀ job ∈ i.2.1, ∀ t ∈ job, t.1 = 1

open Classical in
/-- THREE-PROCESSOR UNIT-TIME JOB-SHOP SCHEDULING, as a decision problem over bitstrings. -/
noncomputable def threeProcessorUnitJobShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING remains NP-complete with `m = 3` processors when every task has
length `1` (`J3|p_ij=1|C_max`).** Source: Lenstra and Rinnooy Kan (1979); Garey and Johnson
(1979), [SS18], comment; Brucker and Knust's classification. -/
public theorem_wanted threeProcessorUnitJobShop_npComplete :
    threeProcessorUnitJobShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorUnitJobShopDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitJobShop
