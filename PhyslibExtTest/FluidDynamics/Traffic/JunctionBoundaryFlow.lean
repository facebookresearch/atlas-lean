/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PhyslibExt.FluidDynamics.Traffic.CumulativeInventory
import PhyslibExt.FluidDynamics.Traffic.JunctionBoundaryFlow

/-!
# Junction boundary flow checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.JunctionBoundaryFlow`:
a two-commodity merge (conservation value `3`, supply bound tight, an
over-supply certificate rejected although each commodity fits alone, and three
different node splits admitted by the same certificate interface), a diverge
(turning fractions `1/4`, `3/4` and the zero-outflow endpoint, signed flows
breaking the factorization), spillback at a jammed first cell with cancellation
and off-junction controls, support and feasibility premise controls, per-commodity
conservation, incidence-bridge values and total-count conservation, route
support with a non-walk control, a loop link, and a two-link series step with
spillback. Owner compatibility is checked against `incidence_mulVec` and the
cumulative inventory telescope.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.CellTransmission
open FluidDynamics.Traffic.JunctionBoundaryFlow
open MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ## Merge: links `0 : 0 → 1`, `1 : 2 → 1`, `2 : 1 → 3`; two commodities. -/

def mTail : Fin 3 → Fin 4 := ![0, 2, 1]
def mHead : Fin 3 → Fin 4 := ![1, 1, 3]
def one3 : Fin 3 → ℝ := fun _ => 1
def kj6 : Fin 3 → ℝ := fun _ => 6
/-- First-cell densities: link 2 half full (supply 3), links 0, 1 empty. -/
def kOpen : Fin 3 → ℝ := ![0, 0, 3]
/-- Link 2 jammed. -/
def kJam : Fin 3 → ℝ := ![0, 0, 6]

private lemma supply_open : supply 1 1 6 3 = 3 := by norm_num [supply, capacity]
private lemma supply_jam : supply 1 1 6 6 = 0 := by norm_num [supply, capacity]

/-- commodity 0 sends 1 from link 0, commodity 1 sends 2 from link 1, both into link 2. -/
noncomputable def qMerge : Fin 2 → Fin 3 → Fin 3 → ℝ := fun c e e' =>
  if c = 0 ∧ e = 0 ∧ e' = 2 then 1 else if c = 1 ∧ e = 1 ∧ e' = 2 then 2 else 0

private lemma qW1_nonneg : ∀ c e e', 0 ≤ qMerge c e e' := by
  intro c e e'; unfold qMerge; split_ifs <;> norm_num

private lemma qW1_support : ∀ c e e', mHead e ≠ mTail e' → qMerge c e e' = 0 := by
  intro c e e' h
  fin_cases c <;> fin_cases e <;> fin_cases e' <;> simp_all [qMerge, mHead, mTail]

private lemma qW1_feasible : IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen qMerge := by
  intro e'
  fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qMerge, mHead, mTail, one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- Merge values: node 1 balances `3 = 3` (nonzero), and link 2 takes exactly its supply `3`. -/
private lemma merge_conservation_value :
    (∑ e with mHead e = 1, ∑ c, linkOutflow qMerge c e) = 3 ∧
    (∑ e with mTail e = 1, ∑ c, linkInflow qMerge c e) = 3 := by
  constructor <;> ((simp only [Finset.sum_filter]) <;> simp only [linkOutflow, linkInflow, qMerge, mHead, mTail, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

private lemma merge_conservation : (∑ e with mHead e = 1, ∑ c, linkOutflow qMerge c e) =
    ∑ e with mTail e = 1, ∑ c, linkInflow qMerge c e :=
  sum_linkOutflow_eq_sum_linkInflow qW1_support 1

private lemma merge_supply_tight :
    ∑ c, linkInflow qMerge c 2 ≤ supply (one3 2) (one3 2) (kj6 2) (kOpen 2) ∧
    ∑ c, linkInflow qMerge c 2 = supply (one3 2) (one3 2) (kj6 2) (kOpen 2) := by
  refine ⟨sum_linkInflow_le_supply qW1_support qW1_feasible 2, ?_⟩
  ((try simp only [Finset.sum_filter]); simp only [linkInflow, qMerge, one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! Oversubscription. Flows `2` and `2` into supply `3`: rejected, though each input alone
fits. -/

noncomputable def qOver : Fin 2 → Fin 3 → Fin 3 → ℝ := fun c e e' =>
  if c = 0 ∧ e = 0 ∧ e' = 2 then 2 else if c = 1 ∧ e = 1 ∧ e' = 2 then 2 else 0

private lemma over_rejected : ¬ IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen qOver := by
  intro h
  have h2 := h 2
  revert h2
  ((simp only [Finset.sum_filter]); simp only [qOver, mHead, mTail, one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

private lemma over_each_fits : qOver 0 0 2 ≤ supply 1 1 6 3 ∧ qOver 1 1 2 ≤ supply 1 1 6 3 := by
  rw [supply_open]; constructor <;> ((try simp only [Finset.sum_filter]) <;> simp only [qOver, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! ## Node-model agnosticism: three different merge outputs for demands `2, 2`, supply `3`. -/

/-- Single-commodity merge certificate from a pair of input flows. -/
noncomputable def qPair (a b : ℝ) : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 2 then a else if e = 1 ∧ e' = 2 then b else 0

private lemma qPair_feasible {a b : ℝ} (hab : a + b ≤ 3) :
    IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen (qPair a b) := by
  intro e'
  fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qPair, mHead, mTail, one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]);
    linarith

private lemma qPair_support (a b : ℝ) : ∀ c e e', mHead e ≠ mTail e' → qPair a b c e e' = 0 := by
  intro c e e' h
  fin_cases e <;> fin_cases e' <;> simp_all [qPair, mHead, mTail]

/-- Daganzo-type priority merge with priority share `1/3` for link 0:
`q0 = mid(2, 3 - 2, 1) = 1`, `q1 = mid(2, 3 - 2, 2) = 2`; demand-proportional merge `1.5, 1.5`;
and a non-maximal (holding) output `0, 0`. All are admitted. -/
private lemma three_node_models_admitted :
    IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen (qPair 1 2) ∧
    IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen (qPair (3 / 2) (3 / 2)) ∧
    IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen (qPair 0 0) :=
  ⟨qPair_feasible (by norm_num), qPair_feasible (by norm_num), qPair_feasible (by norm_num)⟩

/-! ## Diverge: links `0 : 0 → 1`, `1 : 1 → 2`, `2 : 1 → 3`. -/

def dTail : Fin 3 → Fin 4 := ![0, 1, 1]
def dHead : Fin 3 → Fin 4 := ![1, 2, 3]

/-- one commodity, `1` to link 1 and `3` to link 2. -/
noncomputable def qDiverge : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 1 then 1 else if e = 0 ∧ e' = 2 then 3 else 0

private lemma diverge_fractions :
    turningFraction qDiverge () 0 1 = 1 / 4 ∧ turningFraction qDiverge () 0 2 = 3 / 4 ∧
    ∑ e', turningFraction qDiverge () 0 e' = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> ((try simp only [Finset.sum_filter]) <;> simp only [turningFraction, linkOutflow, qDiverge, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- Endpoint: a zero-outflow link has all fractions `0`, so they sum to `0`, not `1`. -/
private lemma diverge_zero_outflow_endpoint : ∑ e', turningFraction qDiverge () 1 e' = 0 := by
  ((try simp only [Finset.sum_filter]); simp only [turningFraction, linkOutflow, qDiverge, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- Fractions sum to one on positive outflow (corollary of T4). -/
private lemma sum_turningFraction_eq_one {E C : Type*} [Fintype E] {q : C → E → E → ℝ} {c : C} {e : E}
    (hnn : ∀ e', 0 ≤ q c e e') (hpos : 0 < linkOutflow q c e) :
    ∑ e', turningFraction q c e e' = 1 := by
  have h : (∑ e', turningFraction q c e e') * linkOutflow q c e = linkOutflow q c e := by
    rw [Finset.sum_mul]
    simp only [turningFraction_mul_linkOutflow hnn]
    rfl
  have hne : linkOutflow q c e ≠ 0 := hpos.ne'
  calc ∑ e', turningFraction q c e e'
      = (∑ e', turningFraction q c e e') * linkOutflow q c e / linkOutflow q c e := by
        rw [mul_div_assoc, div_self hne, mul_one]
    _ = 1 := by rw [h, div_self hne]

/-- Control: a supplied fraction vector that does not sum to one (`0, 1/2, 1/4`) is not the
turning-fraction vector of any nonnegative certificate with positive outflow. -/
private lemma fractions_not_summing_rejected (q : Unit → Fin 3 → Fin 3 → ℝ) (hnn : ∀ e', 0 ≤ q () 0 e')
    (hpos : 0 < linkOutflow q () 0) :
    (fun e' => turningFraction q () 0 e') ≠ ![0, 1 / 2, 1 / 4] := by
  intro h
  have h1 := sum_turningFraction_eq_one hnn hpos
  rw [h] at h1
  revert h1
  ((try simp only [Finset.sum_filter]); simp only [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- Control C4 (T4 without nonnegativity): flows `1, -1` give outflow `0` and break T4. -/
noncomputable def qSigned : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 1 then 1 else if e = 0 ∧ e' = 2 then -1 else 0

private lemma signed_breaks_factorization : turningFraction qSigned () 0 1 * linkOutflow qSigned () 0 ≠ qSigned () 0 1 := by
  ((try simp only [Finset.sum_filter]); simp only [turningFraction, linkOutflow, qSigned, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! ## Spillback and the absence of a FIFO claim (diverge, link 2 jammed). -/

/-- commodity 0 bound for link 1 flows `1`; commodity 1 bound for the jammed link 2 flows
`0`. Feasible, supported, nonnegative: a FIFO diverge would block both; the pin admits it. -/
noncomputable def qJam : Fin 2 → Fin 3 → Fin 3 → ℝ := fun c e e' =>
  if c = 0 ∧ e = 0 ∧ e' = 1 then 1 else 0

private lemma qW4_support : ∀ c e e', dHead e ≠ dTail e' → qJam c e e' = 0 := by
  intro c e e' h
  fin_cases c <;> fin_cases e <;> fin_cases e' <;> simp_all [qJam, dHead, dTail]

private lemma qW4_feasible : IsSupplyFeasible dTail dHead one3 one3 kj6 kJam qJam := by
  intro e'
  fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qJam, dHead, dTail, one3, kj6, kJam, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

private lemma jam_spillback (c : Fin 2) (e : Fin 3) : qJam c e 2 = 0 :=
  eq_zero_of_kFirst_eq_kj (fun c e e' => by unfold qJam; split_ifs <;> norm_num) qW4_support
    qW4_feasible (e' := 2) (by simp [kJam, kj6]) c e

private lemma jam_commodity_order_free : linkOutflow qJam 0 0 = 1 ∧ linkOutflow qJam 1 0 = 0 := by
  constructor <;> ((try simp only [Finset.sum_filter]) <;> simp only [linkOutflow, qJam, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- Control C3 (T3 without nonnegativity): `+1` and `-1` into the jammed link 2 of the merge are
feasible and supported, yet nonzero. -/
noncomputable def qCancel : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 2 then 1 else if e = 1 ∧ e' = 2 then -1 else 0

private lemma cancel_feasible_nonzero :
    IsSupplyFeasible mTail mHead one3 one3 kj6 kJam qCancel ∧
    (∀ c e e', mHead e ≠ mTail e' → qCancel c e e' = 0) ∧ qCancel () 0 2 ≠ 0 := by
  refine ⟨?_, ?_, by simp [qCancel]⟩
  · intro e'
    fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qCancel, mHead, mTail, one3, kj6, kJam, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
  · intro c e e' h
    fin_cases e <;> fin_cases e' <;> simp_all [qCancel, mHead, mTail]

/-- Control (T3 without support): an off-junction flow into the jammed link 2 is unconstrained. -/
noncomputable def qOffJunction : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 2 ∧ e' = 2 then 1 else 0

private lemma offJunction_feasible_nonzero :
    IsSupplyFeasible mTail mHead one3 one3 kj6 kJam qOffJunction ∧ qOffJunction () 2 2 ≠ 0 := by
  refine ⟨?_, by simp [qOffJunction]⟩
  intro e'
  fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qOffJunction, mHead, mTail, one3, kj6, kJam, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! ## Support controls for T1 and T2. -/

/-- a flow from link 2 (head 3) to link 0 (tail 0) breaks conservation at node 3. -/
noncomputable def qTeleport : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 2 ∧ e' = 0 then 1 else 0

private lemma teleport_conservation_fails :
    (∑ e with mHead e = 3, ∑ c, linkOutflow qTeleport c e) = 1 ∧
    (∑ e with mTail e = 3, ∑ c, linkInflow qTeleport c e) = 0 := by
  constructor <;> ((simp only [Finset.sum_filter]) <;> simp only [linkOutflow, linkInflow, qTeleport, mHead, mTail, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- tight junction-local constraint plus an off-junction self-turn into link 2: feasible,
yet the boundary inflow `4` exceeds the supply `3`. -/
noncomputable def qUnbounded : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 2 then 3 else if e = 2 ∧ e' = 2 then 1 else 0

private lemma unbounded_bound_fails :
    IsSupplyFeasible mTail mHead one3 one3 kj6 kOpen qUnbounded ∧
    ∑ c, linkInflow qUnbounded c 2 = 4 ∧ supply (one3 2) (one3 2) (kj6 2) (kOpen 2) = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e'
    fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qUnbounded, mHead, mTail, one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
  · ((try simp only [Finset.sum_filter]); simp only [linkInflow, qUnbounded, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
  · ((try simp only [Finset.sum_filter]); simp only [one3, kj6, kOpen, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! ## Commodity accounting: per-commodity conservation from T1 at `C = Unit`. -/

private lemma perCommodity_conservation {V E C : Type*} [DecidableEq V] [Fintype E]
    {tail head : E → V} {q : C → E → E → ℝ}
    (hq : ∀ c e e', head e ≠ tail e' → q c e e' = 0) (c : C) (v : V) :
    ∑ e with head e = v, linkOutflow q c e = ∑ e with tail e = v, linkInflow q c e := by
  have h := sum_linkOutflow_eq_sum_linkInflow (C := Unit) (q := fun _ => q c)
    (fun _ e e' he => hq c e e' he) v
  simpa [linkOutflow, linkInflow] using h

private lemma merge_perCommodity :
    (∑ e with mHead e = 1, linkOutflow qMerge 0 e) = 1 ∧
    (∑ e with mTail e = 1, linkInflow qMerge 0 e) = 1 ∧
    (∑ e with mHead e = 1, linkOutflow qMerge 1 e) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> ((simp only [Finset.sum_filter]) <;> simp only [linkOutflow, linkInflow, qMerge, mHead, mTail, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-! ## Sign conventions against the owners. -/

/-- T5 on the merge: the movement-network transfer is `+3` into link 2 and `-1`, `-2` out of
links 0 and 1 (inflow minus outflow). -/
private lemma bridge_values :
    (incidenceMatrix (fun m : Fin 3 × Fin 3 => m.1)
        (fun m => m.2)).mulVec (fun m => ∑ c, qMerge c m.1 m.2) 2 = 3 ∧
    (incidenceMatrix (fun m : Fin 3 × Fin 3 => m.1)
        (fun m => m.2)).mulVec (fun m => ∑ c, qMerge c m.1 m.2) 0 = -1 ∧
    (incidenceMatrix (fun m : Fin 3 × Fin 3 => m.1)
        (fun m => m.2)).mulVec (fun m => ∑ c, qMerge c m.1 m.2) 1 = -2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [incidenceMatrix_mulVec_turningFlow] <;> ((try simp only [Finset.sum_filter]) <;> simp only [linkInflow, linkOutflow, qMerge, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique] <;> norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

/-- T5 stated with the owner `incidenceMatrix` (the integration swap): same statement, closed by
T5 because the two definitions are definitionally equal. -/
private lemma T5_with_owner_incidenceMatrix {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    (q : C → E → E → ℝ) (e : E) :
    (MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix (fun m : E × E => m.1)
        (fun m => m.2)).mulVec (fun m => ∑ c, q c m.1 m.2) e =
      ∑ c, linkInflow q c e - ∑ c, linkOutflow q c e :=
  incidenceMatrix_mulVec_turningFlow q e

/-- Owner `incidence_mulVec` on the movement network gives the same right side (sign check). -/
private lemma owner_incidence_mulVec_movement {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    (q : C → E → E → ℝ) (e : E) :
    (∑ m ∈ (Finset.univ : Finset (E × E)).filter (fun m => m.2 = e), ∑ c, q c m.1 m.2) -
      (∑ m ∈ (Finset.univ : Finset (E × E)).filter (fun m => m.1 = e), ∑ c, q c m.1 m.2) =
      ∑ c, linkInflow q c e - ∑ c, linkOutflow q c e := by
  rw [← MathlibExt.Combinatorics.Graph.ArcNetwork.incidence_mulVec]
  exact incidenceMatrix_mulVec_turningFlow q e

/-- End-to-end bridge: a junction step `N' = N + dt * (inflow - outflow)` on link counts is the
owner stock update `N' = N + B *ᵥ F` on the movement network with `F = dt * turning flows`, so
the owner `stock_level_arc_balance` conserves the total link vehicle count. -/
private lemma junction_step_conserves_total {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    (q : C → E → E → ℝ) (dt : ℝ) (N N' : E → ℝ)
    (hstep : ∀ e, N' e = N e + dt * (∑ c, linkInflow q c e - ∑ c, linkOutflow q c e)) :
    ∑ e, N' e = ∑ e, N e := by
  have h5 : ∀ e, (MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix
      (fun m : E × E => m.1) (fun m => m.2)).mulVec (fun m => ∑ c, dt * q c m.1 m.2) e =
      ∑ c, linkInflow (fun c a b => dt * q c a b) c e -
        ∑ c, linkOutflow (fun c a b => dt * q c a b) c e :=
    fun e => T5_with_owner_incidenceMatrix (fun c a b => dt * q c a b) e
  have h6 : ∀ e, ∑ c, linkInflow (fun c a b => dt * q c a b) c e -
      ∑ c, linkOutflow (fun c a b => dt * q c a b) c e =
      dt * (∑ c, linkInflow q c e - ∑ c, linkOutflow q c e) := by
    intro e
    simp only [linkInflow, linkOutflow, ← Finset.mul_sum, mul_sub]
  have hupd : N' = N + (MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix
      (fun m : E × E => m.1) (fun m => m.2)).mulVec (fun m => ∑ c, dt * q c m.1 m.2)
      + (0 : E → ℝ) - 0 := by
    funext e
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, add_zero, sub_zero]
    rw [h5 e, h6 e, hstep e]
  have h := MathlibExt.Combinatorics.Graph.ArcNetwork.stock_level_arc_balance
    (fun m : E × E => m.1) (fun m => m.2) _ hupd
  simpa using h

/-- CumulativeInventory sign: link counts driven by the bridge satisfy the owner step balance
`N (j+1) = N j + dt * (Fin j - Fout j)` with `Fin = ∑ c, linkInflow`, `Fout = ∑ c, linkOutflow`,
so the owner inventory identity applies verbatim. -/
private lemma cumulative_from_bridge {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]
    (q : ℕ → C → E → E → ℝ) (dt : ℝ) (hdt : 0 ≤ dt) (N : ℕ → E → ℝ) (e : E)
    (hstep : ∀ j, N (j + 1) e = N j e + dt * (incidenceMatrix
      (fun m : E × E => m.1) (fun m => m.2)).mulVec (fun m => ∑ c, q j c m.1 m.2) e)
    (n : ℕ) :
    N n e = N 0 e + (∑ j ∈ Finset.range n, dt * ∑ c, linkInflow (q j) c e)
      - ∑ j ∈ Finset.range n, dt * ∑ c, linkOutflow (q j) c e :=
  FluidDynamics.Traffic.CumulativeInventory.cumulative_link_inventory (fun j => N j e) (fun j => ∑ c, linkInflow (q j) c e)
    (fun j => ∑ c, linkOutflow (q j) c e) dt hdt
    (fun j => by rw [hstep j, incidenceMatrix_mulVec_turningFlow]) n

/-! ## Routes (T6). -/

private lemma route_walk : IsArcWalk mTail mHead 0 3 [0, 2] := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro e he
    rw [List.head?_cons, Option.mem_some_iff] at he
    subst he; simp [mTail]
  · simp [mHead, mTail]
  · intro e he
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at he
    subst he; simp [mHead]

/-- Route-consistent certificate: flow only from link 0 to link 2 along `[0, 2]`; T6 gives
support. -/
noncomputable def qRoute : Unit → Fin 3 → Fin 3 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 2 then 1 else 0

private lemma route_support (e e' : Fin 3) (hne : mHead e ≠ mTail e') : qRoute () e e' = 0 :=
  eq_zero_of_route (orig := fun _ => (0 : Fin 4)) (dest := fun _ => 3)
    (edges := fun _ => [0, 2]) (fun _ => route_walk)
    (fun c e e' h => by
      unfold qRoute at h
      split_ifs at h with h1
      · obtain ⟨rfl, rfl⟩ := h1; simp
      · exact absurd rfl h) hne

/-- Control C5: the list `[0, 1]` (head of link 0 is node 1, tail of link 1 is node 2) is not a
walk; a flow consistent with it joins non-adjacent links, so support fails. -/
private lemma not_walk_unsupported :
    ¬ (IsArcWalk mTail mHead 0 1 [0, 1]) ∧ mHead 0 ≠ mTail 1 := by
  refine ⟨?_, by simp [mHead, mTail]⟩
  rintro ⟨-, -, hc, -⟩
  simp [mHead, mTail] at hc

/-! ## Loop handling: a loop link turning into itself is balanced in T1 and vanishes in T5. -/

def lTail : Fin 1 → Fin 1 := fun _ => 0
def lHead : Fin 1 → Fin 1 := fun _ => 0
noncomputable def qLoop : Unit → Fin 1 → Fin 1 → ℝ := fun _ _ _ => 5

private lemma loop_values :
    (incidenceMatrix (fun m : Fin 1 × Fin 1 => m.1)
        (fun m => m.2)).mulVec (fun m => ∑ c, qLoop c m.1 m.2) 0 = 0 ∧
    (∑ e with lHead e = 0, ∑ c, linkOutflow qLoop c e) = 5 ∧
    (∑ e with lTail e = 0, ∑ c, linkInflow qLoop c e) = 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [incidenceMatrix_mulVec_turningFlow]; ((try simp only [Finset.sum_filter]); simp only [linkInflow, linkOutflow, qLoop, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
  · ((simp only [Finset.sum_filter]); simp only [linkOutflow, qLoop, lHead, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
  · ((simp only [Finset.sum_filter]); simp only [linkInflow, qLoop, lTail, Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_one, Fintype.sum_unique]; norm_num [Finset.sum_filter, Fin.sum_univ_two, Fin.sum_univ_three, Finset.mem_filter,
      Finset.mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])


/-! ## Coupled two-link witness (series: link `0 : 0 → 1`, link `1 : 1 → 2`). -/

def sTail : Fin 2 → Fin 3 := ![0, 1]
def sHead : Fin 2 → Fin 3 := ![1, 2]
def one2 : Fin 2 → ℝ := fun _ => 1
def kj2 : Fin 2 → ℝ := fun _ => 6
def kS : Fin 2 → ℝ := ![0, 3]
def kSjam : Fin 2 → ℝ := ![0, 6]
noncomputable def qS (a : ℝ) : Unit → Fin 2 → Fin 2 → ℝ := fun _ e e' =>
  if e = 0 ∧ e' = 1 then a else 0

private lemma series_feasible : IsSupplyFeasible sTail sHead one2 one2 kj2 kS (qS 2) := by
  intro e'
  fin_cases e' <;> ((simp only [Finset.sum_filter]) <;> simp only [qS, sHead, sTail, one2, kj2,
    kS, supply, capacity, Finset.sum_filter, Fin.sum_univ_two, Fintype.sum_unique] <;>
    norm_num [Finset.sum_filter, Fin.sum_univ_two, Finset.mem_filter, Finset.mem_univ,
      true_and, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])

private lemma series_support (a : ℝ) : ∀ c e e', sHead e ≠ sTail e' → qS a c e e' = 0 := by
  intro c e e' h
  fin_cases e <;> fin_cases e' <;> simp_all [qS, sHead, sTail]

/-- Counts `N = (5, 1)`, one step `dt = 1` with junction flow `2` into link 1 (supply `3`):
`N' = (3, 3)` through the bridge, total `6` conserved. -/
private lemma series_step :
    let F := fun m : Fin 2 × Fin 2 => ∑ c, qS 2 c m.1 m.2
    let B := incidenceMatrix (fun m : Fin 2 × Fin 2 => m.1)
      (fun m => m.2)
    (5 + 1 * B.mulVec F 0 = 3) ∧ (1 + 1 * B.mulVec F 1 = 3) := by
  intro F B
  refine ⟨?_, ?_⟩ <;> simp only [F, B, incidenceMatrix_mulVec_turningFlow] <;>
    ((try simp only [Finset.sum_filter]) <;> simp only [linkInflow, linkOutflow, qS,
      Fin.sum_univ_two, Fintype.sum_unique] <;> norm_num)

/-- With link 1 jammed the junction flow must vanish (spillback), so both counts stay put. -/
private lemma series_spillback (a : ℝ) (ha : 0 ≤ a)
    (hR : IsSupplyFeasible sTail sHead one2 one2 kj2 kSjam (qS a)) : a = 0 := by
  have h := eq_zero_of_kFirst_eq_kj (fun c e e' => by unfold qS; split_ifs <;> linarith)
    (series_support a) hR (e' := 1) (by simp [kSjam, kj2]) () 0
  simpa [qS] using h

#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.sum_linkOutflow_eq_sum_linkInflow
#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.sum_linkInflow_le_supply
#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.eq_zero_of_kFirst_eq_kj
#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.turningFraction_mul_linkOutflow
#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.incidenceMatrix_mulVec_turningFlow
#print axioms FluidDynamics.Traffic.JunctionBoundaryFlow.eq_zero_of_route
