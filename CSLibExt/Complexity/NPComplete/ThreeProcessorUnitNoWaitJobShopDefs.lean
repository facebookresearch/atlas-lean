/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING (J3|p_ij=1;no-wait|Cmax): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING (the
parent problem) and problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING (the no-wait condition
`σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`);
C. Sriskandarajah and P. Ladet, "Some no-wait shops scheduling problems: complexity aspect",
European Journal of Operational Research 24 (1986), 424-438,
doi:10.1016/0377-2217(86)90036-6;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_now`, entry
`J3|p_ij=1;no-wait|C_max` (minimal NP-hard in the strong sense, citing Sriskandarajah and
Ladet 1986).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeProcessorEqualLengthJobShopDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShop

open JobShopScheduling (JobShopSchedulingInstance taskLength taskProcessor)

/-- Well-formedness of an instance: the instance is a well-formed THREE-PROCESSOR JOB-SHOP
SCHEDULING instance with equal task lengths (a well-formed [SS18] instance with `m = 3` whose
tasks all have one length), and every task has length `1`. -/
def WellFormed (i : JobShopSchedulingInstance) : Prop :=
  ThreeProcessorEqualLengthJobShop.RestrictedWellFormed i ∧ ∀ job ∈ i.2.1, ∀ t ∈ job, t.1 = 1

/-- There is a no-wait job-shop schedule meeting the deadline: start times `σ` that are
one-to-one on the tasks of each processor, such that a task of a processor starting after
another task `t'` of that processor starts no earlier than `t'` finishes, each task of a job
starts exactly when the previous task of that job finishes, and the last task of every job
finishes by `D`. -/
def ThreeProcessorUnitNoWaitJobShopFeasible (i : JobShopSchedulingInstance) : Prop :=
  ∃ σ : JobShopScheduling.Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength i ⟨j, k⟩) ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ i.2.2

open Classical in
/-- THREE-PROCESSOR UNIT-TIME NO-WAIT JOB-SHOP SCHEDULING as a decision problem over
bitstrings. -/
noncomputable def threeProcessorUnitNoWaitJobShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeProcessorUnitNoWaitJobShopFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitNoWaitJobShop
