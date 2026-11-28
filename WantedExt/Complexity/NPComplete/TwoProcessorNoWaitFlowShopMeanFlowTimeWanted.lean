/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: with a bound `K` on the sum of the completion times in place of the deadline,
the problem is NP-complete in the strong sense for `m` arbitrary, and open for fixed `m ≥ 2`);
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (`F2|no-wait|∑ Cⱼ` is NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMeanFlowTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMeanFlowTime

/-!
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of `m = 2` tasks `t₁[j], t₂[j]` (with
`tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task `t`, and a
bound `K ∈ ℤ⁺`. QUESTION: is there a flow-shop schedule for `J` with the property that, for each
`j ∈ J`, `σ₂(j) = σ₁(j) + l(t₁[j])`, such that the sum, over all `j ∈ J`, of
`σ₂(j) + l(t₂[j])` is at most `K`?

This is NO-WAIT FLOW-SHOP MEAN FLOW TIME (Garey and Johnson's comment to [SS16],
`NoWaitFlowShopMeanFlowTimeWanted`) restricted to instances with exactly two processors
(`F2|no-wait|∑ Cⱼ`). Garey and Johnson record the problem as open for every fixed `m ≥ 2`;
Röck (1984) proved the two-processor case NP-hard in the strong sense. The instance type,
`NoWaitFlowShopScheduling.WellFormed` and
`NoWaitFlowShopMeanFlowTime.NoWaitFlowShopMeanFlowTimeFeasible` are the parent's, unchanged;
`WellFormed` adds that the instance's number of processors is `2`. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR NO-WAIT FLOW-SHOP MEAN FLOW TIME is NP-complete.** Source: Garey and Johnson
(1979), [SS16], comment (open for fixed `m ≥ 2`); Röck (1984). -/
public theorem_wanted twoProcessorNoWaitFlowShopMeanFlowTime_npComplete :
    twoProcessorNoWaitFlowShopMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitFlowShopMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMeanFlowTime
