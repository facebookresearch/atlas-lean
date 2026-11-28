/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH PRECEDENCE AND UNIT TIMES (OMPT|prec; p_ij = 1|C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (shop problems with
multiprocessor tasks: the MPT open-shop model) and Section 1.3 (precedence relations);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT|prec; p_ij = 1|C_max` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (2003).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Finset.Nat
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultiprocessorTaskFlowShopPrecedenceMakespan
  (MultiprocessorTaskFlowShopPrecedenceMakespanInstance WellFormed)

/-- `σ` (start times) is an MPT open-shop schedule of `n` jobs with processing times `p i s`
and stage machine sets `μ`: two different operations of one job occupy disjoint time intervals
`[σ i s, σ i s + p i s)`, and so do two different operations whose machine sets share a
machine. -/
def IsMPTOpenShopSchedule {n : ℕ} (μ : List (List ℕ)) (p σ : Fin n → Fin μ.length → ℕ) :
    Prop :=
  (∀ i s s', s ≠ s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i s') (σ i s' + p i s'))) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → (∃ k, k ∈ μ.get s ∧ k ∈ μ.get s') →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- `σ` is an MPT open-shop schedule of `n` unit-time jobs (`p_ij = 1`) with stage machine sets
`μ` that obeys the precedence constraints of the listed arcs: if `i → k`, then no operation of
`k` starts before `C_i`. -/
def IsMPTOpenShopPrecedenceSchedule {n : ℕ} (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) : Prop :=
  IsMPTOpenShopSchedule μ (fun _ _ => 1) σ ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- Some MPT open-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultiprocessorTaskOpenShopPrecedenceMakespanFeasible
    (i : MultiprocessorTaskFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Fin i.2.2.1.length → Fin i.2.1.length → ℕ,
    IsMPTOpenShopPrecedenceSchedule i.2.1 i.2.2.2.1 σ ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `OMPT|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorTaskFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopPrecedenceMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespan
