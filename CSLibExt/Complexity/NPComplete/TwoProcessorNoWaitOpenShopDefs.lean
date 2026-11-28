/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
comment on p. 242 ("The analogous "no-wait" versions of OPEN-SHOP SCHEDULING and JOB-SHOP
SCHEDULING are NP-complete in the strong sense for m = 2 [Sahni and Cho, 1977b]");
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShop

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance with two
processors. -/
def WellFormed (i : OpenShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 2

/-- An open-shop schedule meeting the deadline in which every job runs its tasks back to back:
one task starts exactly when the job's task on the other processor ends. -/
def TwoProcessorNoWaitOpenShopFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsOpenShopSchedule i σ ∧
    ∀ j, ∃ p q : Fin i.1, p ≠ q ∧ σ q j = σ p j + taskLength i p j

open Classical in
/-- TWO-PROCESSOR NO-WAIT OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitOpenShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitOpenShopFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShop
