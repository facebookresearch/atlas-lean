/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "Open for fixed `m = 3`");
H. Röck, "The three-machine no-wait flow shop is NP-complete", Journal of the ACM 31 (1984),
336-345, doi:10.1145/62.65.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorNoWaitFlowShop

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

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorNoWaitFlowShop
