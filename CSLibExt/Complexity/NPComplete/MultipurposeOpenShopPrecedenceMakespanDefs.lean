/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPM|prec; p_ij = 1|C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5:
Chapter 10 (the MPM flow-shop and open-shop models), Section 1.3 (precedence relations) and
Table 5.3 (`P|p_i = 1; prec|C_max` is NP-hard in the strong sense, Ullman);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense, citing
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (MultipurposeFlowShopPrecedenceMakespanInstance
  WellFormed Job Stage Prec completionTime)

/-- `σ` (start times) and `a` (machines) form an MPM open-shop schedule of `n` jobs with
processing times `p i s` on `m` machines with stage machine sets `μ`: each operation `(i, s)`
runs on a machine of `μ_s`; two different operations of the same job occupy disjoint time
intervals `[σ i s, σ i s + p i s)`; and two different operations on the same machine occupy
disjoint time intervals. -/
def IsMPMOpenShopSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (p : Fin n → Fin μ.length → ℕ)
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  (∀ i s, (a i s : ℕ) ∈ μ.get s) ∧
    (∀ i s s', s ≠ s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i s') (σ i s' + p i s'))) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → a i s = a i' s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` and `a` form an MPM open-shop schedule of `n` unit-time jobs (`p_ij = 1`) on `m`
machines with stage machine sets `μ` that obeys the precedence constraints of the listed pairs:
if `i → k`, then no operation of `k` starts before `C_i`. -/
def IsMPMOpenShopPrecedenceSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  IsMPMOpenShopSchedule m μ (fun _ _ => 1) σ a ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- Some MPM open-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultipurposeOpenShopPrecedenceMakespanFeasible
    (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPM|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespan
