/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O|p_ij=1;t_kl=t_lk|Cmax: definitions

Source:
V. J. Rayward-Smith and D. Rebaine, "Open shop scheduling with delays", RAIRO Informatique
théorique et Applications 26 (1992), 439-447, doi:10.1051/ita/1992260504391, Section 2,
problem OmDU and Theorem 2 ("OmDU is NP-complete even if the delays are symmetric");
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems
with transportation delays" (University of Osnabrück,
http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem `O|p_ij=1;t_kl=t_lk|C_max`,
minimal strongly NP-hard, credited to Rayward-Smith and Rebaine (1992).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopSymmetricTransportationDelays

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-- An instance: an OPEN-SHOP SCHEDULING instance (the number `m` of machines, the jobs as lists
of task lengths, the bound `K`) and the delay matrix, row `k` listing `t_k0, …, t_k(m-1)`. -/
abbrev UnitOpenShopSymmetricTransportationDelaysInstance :=
  OpenShopSchedulingInstance × List (List ℕ)

/-- The transportation delay `t_kl` from machine `k` to machine `l`. -/
def delay (i : UnitOpenShopSymmetricTransportationDelaysInstance) (k l : Fin i.1.1) : ℕ :=
  (i.2.getD k []).getD l 0

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance (`m ≥ 1`, `m`
tasks per job, `K ≥ 1`) whose tasks all have length `1`, with an `m × m` symmetric delay matrix
whose diagonal is `0`. -/
def WellFormed (i : UnitOpenShopSymmetricTransportationDelaysInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i.1 ∧ (∀ job ∈ i.1.2.1, ∀ l ∈ job, l = 1) ∧
    i.2.length = i.1.1 ∧ (∀ row ∈ i.2, row.length = i.1.1) ∧
    (∀ k l, delay i k l = delay i l k) ∧ ∀ k, delay i k k = 0

/-- Some open-shop schedule meeting the makespan bound `K` respects the delays: if job `j`'s
task on machine `q ≠ p` starts no earlier than its task on machine `p`, it starts at least
`t_pq` after that task is completed. -/
def UnitOpenShopSymmetricTransportationDelaysFeasible
    (i : UnitOpenShopSymmetricTransportationDelaysInstance) : Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsOpenShopSchedule i.1 σ ∧
    ∀ j p q, p ≠ q → σ p j ≤ σ q j → σ p j + taskLength i.1 p j + delay i p q ≤ σ q j

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O|p_ij=1;t_kl=t_lk|C_max` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopSymmetricTransportationDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitOpenShopSymmetricTransportationDelaysInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopSymmetricTransportationDelaysFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopSymmetricTransportationDelays
