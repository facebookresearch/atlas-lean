/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O2|no-wait|ΣC_i: definitions

Source:
W. Kubiak, C. Sriskandarajah and K. Zaras, "A note on the complexity of openshop scheduling
problems", INFOR 29 (1991), 284-294, doi:10.1080/03155986.1991.11732176 (abstract: "The problem
of minimizing mean flow time in no-wait openshop ... [is] shown to be NP-hard"; the full text was
not available); recorded as strongly NP-hard (a minimal NP-hard problem) in P. Brucker and
S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems with nowait"
(University of Osnabrück, http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem
`O2|no-wait|ΣC_i`, credited to Kubiak et al. (1991).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShopTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-- Well-formedness of an instance: two machines, and every job consists of two tasks. -/
def WellFormed (i : OpenShopSchedulingInstance) : Prop :=
  i.1 = 2 ∧ ∀ job ∈ i.2.1, job.length = i.1

/-- Some no-wait open-shop schedule has total completion time at most `K`: one task of each job
starts exactly when the job's other task ends, and the completion times
`C_j = max_p (σ p j + l(t_p[j]))` sum to at most `K`. -/
def TwoProcessorNoWaitOpenShopTotalCompletionFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsOpenShopSchedule i σ ∧
    (∀ j, ∃ p q : Fin i.1, p ≠ q ∧ σ q j = σ p j + taskLength i p j) ∧
    ∑ j, Finset.univ.sup (fun p => σ p j + taskLength i p j) ≤ i.2.2

open Classical in
/-- NO-WAIT OPEN SHOP `O2|no-wait|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitOpenShopTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitOpenShopTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitOpenShopTotalCompletion
