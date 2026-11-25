/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BridgeTorchTwo
import Mathlib.Data.Finset.Powerset

/-! # Initial values for the bridge and torch problem with capacity three

The theorem `bridgeTime_three_initial_values` gives the optimal times for one through six
people. Explicit schedules attain the six values, and a finite search excludes cheaper schedules.
-/

set_option autoImplicit false

namespace MetaMathlibExt.BridgeTorchGeneralizations

open Finset

-- Everyone still on the left has to cross at least once.
private theorem slowest_le_cost {c : ℕ} {P L : Finset ℕ} {left : Bool} {σ : List (Finset ℕ)}
    (hσ : bridgeScheduleFrom c P L left σ = true) : L.sup id ≤ scheduleCost σ := by
  induction σ generalizing L left with
  | nil =>
    simp [bridgeScheduleFrom] at hσ
    simp [hσ.1, scheduleCost]
  | cons A σ ih =>
    change L.sup id ≤ A.sup id + scheduleCost σ
    cases left <;> simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq] at hσ
    · exact (sup_mono (subset_union_left (s₂ := A))).trans
        ((ih hσ.2).trans (Nat.le_add_left _ _))
    · apply Finset.sup_le
      intro p hp
      by_cases ha : p ∈ A
      · exact (le_sup (f := id) ha).trans (Nat.le_add_right _ _)
      · exact (le_sup (f := id) (mem_sdiff.mpr ⟨hp, ha⟩)).trans
          ((ih hσ.2).trans (Nat.le_add_left _ _))

-- Search for a completion within the budget. At depth zero any unfinished prefix is accepted,
-- so failure rules out even schedules longer than the search depth.
private def mayFinish (P : Finset ℕ) : ℕ → Finset ℕ → Bool → ℕ → Bool
  | 0, _, _, _ => true
  | depth + 1, L, left, budget =>
    decide (L.sup id ≤ budget ∧ ((L = ∅ ∧ left = false) ∨
      ∃ A ∈ (if left then L else P \ L).powerset, A.Nonempty ∧ A.card ≤ 3 ∧ A.sup id ≤ budget ∧
        mayFinish P depth (if left then L \ A else L ∪ A) (!left) (budget - A.sup id) = true))

private theorem mayFinish_of_schedule {P L : Finset ℕ} {left : Bool} {σ : List (Finset ℕ)}
    {budget : ℕ} (depth : ℕ) (hσ : bridgeScheduleFrom 3 P L left σ = true)
    (hc : scheduleCost σ ≤ budget) : mayFinish P depth L left budget = true := by
  induction depth generalizing L left σ budget with
  | zero => rfl
  | succ depth ih =>
    rw [mayFinish, decide_eq_true_eq]
    refine ⟨(slowest_le_cost hσ).trans hc, ?_⟩
    cases σ with
    | nil =>
      left
      simpa [bridgeScheduleFrom] using hσ
    | cons A σ =>
      right
      have hcost : A.sup id + scheduleCost σ ≤ budget := hc
      cases left <;> simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq] at hσ
      all_goals
        exact ⟨A, mem_powerset.mpr hσ.1.2.2, hσ.1.1, hσ.1.2.1, by omega,
          ih hσ.2 (by omega)⟩

private theorem bridgeTime_eq_of_search {n cost : ℕ} {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule 3 n σ) (hc : scheduleCost σ = cost)
    (hsearch : mayFinish (Icc 1 n) cost (Icc 1 n) true (cost - 1) = false) :
    bridgeTime 3 n = cost := by
  apply le_antisymm (hc ▸ bridgeTime_le_scheduleCost hσ)
  unfold bridgeTime
  refine le_csInf (s := {t | ∃ τ, IsBridgeSchedule 3 n τ ∧ scheduleCost τ = t})
    ⟨_, σ, hσ, rfl⟩ ?_
  rintro _ ⟨τ, hτ, rfl⟩
  by_contra! hlt
  have h := mayFinish_of_schedule cost hτ (show scheduleCost τ ≤ cost - 1 by omega)
  simp [hsearch] at h

/-- **Initial values for capacity three.** Let $T_3(n)$ be the optimal crossing time of $n$
people with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. Then
$T_3(1) = 1$, $T_3(2) = 2$, $T_3(3) = 3$, $T_3(4) = 7$, $T_3(5) = 9$ and $T_3(6) = 14$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 8 (`jis-2026-26.5.6-prop-8`). -/
public theorem bridgeTime_three_initial_values :
    bridgeTime 3 1 = 1 ∧ bridgeTime 3 2 = 2 ∧ bridgeTime 3 3 = 3 ∧ bridgeTime 3 4 = 7 ∧
      bridgeTime 3 5 = 9 ∧ bridgeTime 3 6 = 14 := by
  refine ⟨bridgeTime_eq_of_search (σ := [{1}]) ?_ ?_ ?_,
    bridgeTime_eq_of_search (σ := [{1, 2}]) ?_ ?_ ?_,
    bridgeTime_eq_of_search (σ := [{1, 2, 3}]) ?_ ?_ ?_,
    bridgeTime_eq_of_search (σ := [{1, 2}, {1}, {1, 3, 4}]) ?_ ?_ ?_,
    bridgeTime_eq_of_search (σ := [{1, 2, 3}, {1}, {1, 4, 5}]) ?_ ?_ ?_,
    bridgeTime_eq_of_search (σ := [{1, 2}, {1}, {4, 5, 6}, {2}, {1, 2, 3}]) ?_ ?_ ?_⟩
  all_goals
    try unfold IsBridgeSchedule
    decide +kernel

end MetaMathlibExt.BridgeTorchGeneralizations
