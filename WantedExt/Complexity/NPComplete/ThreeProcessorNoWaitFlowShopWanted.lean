/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "Open for fixed `m = 3`");
H. Röck, "The three-machine no-wait flow shop is NP-complete", Journal of the ACM 31 (1984),
336-345, doi:10.1145/62.65.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.NoWaitFlowShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorNoWaitFlowShop

/-!
# THREE-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of `m = 3` tasks `t₁[j], t₂[j], t₃[j]`
(with `tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task `t`,
and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there a flow-shop schedule for `J` that meets
the overall deadline and has the property that, for each `j ∈ J` and `1 ≤ i < 3`,
`σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`?

This is the restriction of NO-WAIT FLOW-SHOP SCHEDULING ([SS16],
`NoWaitFlowShopSchedulingWanted`) to `m = 3`, which Garey and Johnson list as open and Röck
proved NP-complete in the strong sense. The instance type,
`NoWaitFlowShopScheduling.WellFormed` and
`NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingFeasible` are the parent's, unchanged;
`WellFormed` adds `m = 3`. Röck states the result for the permutation flow shop; with
one-to-one one-processor schedules a no-wait schedule processes the jobs in the same order on
every processor, so the no-wait problem is the permutation problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (`0 < m`, every job has `m` tasks, `0 < D`)
and `m = 3`. -/
def WellFormed (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 3

open Classical in
/-- THREE-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def threeProcessorNoWaitFlowShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingFeasible i)
  | none => false

/-- **THREE-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson
(1979), [SS16], comment; Röck (1984). -/
public theorem_wanted threeProcessorNoWaitFlowShop_npComplete :
    threeProcessorNoWaitFlowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorNoWaitFlowShopDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorNoWaitFlowShop
