/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MEAN FLOW TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: with a bound `K` on the sum of the completion times in place of the deadline,
the problem is NP-complete in the strong sense for `m` arbitrary, and open for fixed `m ≥ 2`);
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (`F2|no-wait|∑ Cⱼ` is NP-hard in the strong sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopMeanFlowTimeDefs
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMeanFlowTime

/-- Well-formedness of an instance: the parent's (`0 < m`, every job has `m` tasks, `0 < K`)
and the instance has exactly `m = 2` processors. -/
def WellFormed (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 2

open Classical in
/-- TWO-PROCESSOR NO-WAIT FLOW-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitFlowShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      NoWaitFlowShopMeanFlowTime.NoWaitFlowShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMeanFlowTime
