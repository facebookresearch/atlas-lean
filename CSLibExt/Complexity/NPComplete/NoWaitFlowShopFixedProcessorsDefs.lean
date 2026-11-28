/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT FLOW-SHOP SCHEDULING with a fixed number `m ≥ 4` of processors: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: "NP-complete in the strong sense for any fixed `m ≥ 4`", credited to
Papadimitriou and Kanellakis);
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited temporary
storage", Journal of the ACM 27 (1980), 533-549, doi:10.1145/322203.322213.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopFixedProcessors

/-- Well-formedness of an instance for the fixed number `m` of processors: the parent's
(`0 < m`, every job has `m` tasks, `0 < D`) and the instance has exactly `m` processors. -/
def WellFormed (m : ℕ) (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) :
    Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = m

open Classical in
/-- NO-WAIT FLOW-SHOP SCHEDULING with the number of processors fixed to `m`, as a decision
problem over bitstrings. -/
noncomputable def noWaitFlowShopFixedProcessorsDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (WellFormed m i ∧
      NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopFixedProcessors
