/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP SCHEDULING with equal task lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment: "If in the nonpreemptive case all tasks have the same length, the problem
is NP-complete for `m = 3`";
J. K. Lenstra and A. H. G. Rinnooy Kan, "Computational complexity of discrete optimization
problems", Annals of Discrete Mathematics 4 (1979), 121-140,
doi:10.1016/S0167-5060(08)70821-5 (cited by Garey and Johnson as [Lenstra and Rinnooy Kan,
1978b]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShop

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# THREE-PROCESSOR JOB-SHOP SCHEDULING with equal task lengths is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of an ordered collection of tasks
`t_k[j]`, `1 ≤ k ≤ n_j`, all of the same length `l(t) = ℓ ∈ ℤ₀⁺`, for each task `t` a processor
`p(t) ∈ {1, 2, 3}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and a
deadline `D ∈ ℤ⁺`. QUESTION: is there a (nonpreemptive) job-shop schedule for `J` on the
`m = 3` processors that meets the overall deadline `D`?

This is the restriction of JOB-SHOP SCHEDULING
(`WantedExt.Complexity.NPComplete.JobShopSchedulingWanted`), whose schedules are nonpreemptive,
to instances with `m = 3` processors in which all tasks have the same length. The instance
type, its `WellFormed` and `JobShopSchedulingFeasible` are reused unchanged; the restriction
is added to well-formedness. The common length is part of the instance; the unit-length
instances (`ℓ = 1`) are among them.

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
SCHEDULING instance, `m = 3`, and all tasks have the same length `ℓ`. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ ∃ ℓ, ∀ job ∈ i.2.1, ∀ t ∈ job, t.1 = ℓ

open Classical in
/-- THREE-PROCESSOR JOB-SHOP SCHEDULING with equal task lengths, as a decision
problem over bitstrings. -/
noncomputable def threeProcessorEqualLengthJobShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING remains NP-complete with `m = 3` processors when all tasks have the
same length.** Source: Garey and Johnson (1979), [SS18], comment; Lenstra and Rinnooy Kan
(1979). -/
public theorem_wanted threeProcessorEqualLengthJobShop_npComplete :
    threeProcessorEqualLengthJobShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorEqualLengthJobShopDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShop
