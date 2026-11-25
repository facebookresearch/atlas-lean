/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.QueueOccupancyArea
import Mathlib.Tactic.NormNum

/-! # A finite-window example with out-of-order departures -/

open Filter MeasureTheory Set

-- Two customers arrive at zero, the second leaves first, and later arrivals have zero sojourn.
example :
    let a (i : ℕ) : ℝ := ((i - 1 : ℕ) : ℝ)
    let w (i : ℕ) : ℝ := if i = 0 then 4 else if i = 1 then 1 else 0
    (∫ s in (0 : ℝ)..2, ({i | a i ≤ s ∧ s < a i + w i}.ncard : ℝ)) = 3 := by
  let a (i : ℕ) : ℝ := ((i - 1 : ℕ) : ℝ)
  let w (i : ℕ) : ℝ := if i = 0 then 4 else if i = 1 then 1 else 0
  change (∫ s in (0 : ℝ)..2, ({i | a i ≤ s ∧ s < a i + w i}.ncard : ℝ)) = 3
  have hmono : Monotone a := fun _ _ h => Nat.cast_le.mpr (Nat.sub_le_sub_right h 1)
  have htop : Tendsto a atTop atTop := by
    refine tendsto_atTop.2 fun r => ?_
    obtain ⟨k, hk⟩ := exists_nat_ge r
    exact eventually_atTop.2 ⟨k + 1, fun i hi => hk.trans (Nat.cast_le.mpr (by omega))⟩
  have hnonneg : ∀ i, 0 ≤ w i := by
    intro i
    unfold w
    split <;> (try split) <;> positivity
  have hn : {i | a i ≤ (2 : ℝ)}.ncard = 4 := by
    have h : {i | a i ≤ (2 : ℝ)} = (Finset.range 4 : Set ℕ) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range, a, ← Nat.cast_ofNat (R := ℝ),
        Nat.cast_le]
      omega
    rw [h, Set.ncard_coe_finset, Finset.card_range]
  have h := (MetaMathlibExt.integral_queueOccupancy_eq_and_bounds
    (a := a) (w := w) (fun i => Nat.cast_nonneg _) hmono htop hnonneg (t := 2) (by norm_num)).1
  rw [h, hn]
  norm_num [Finset.sum_range_succ, a, w, min_def]
