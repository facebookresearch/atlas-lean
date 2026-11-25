/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-! # Area under a queue's occupancy path -/

open Filter MeasureTheory Set

namespace MetaMathlibExt

@[expose] public section

/-- **Area under the number-in-system path.** Let $a_i \ge 0$ be nondecreasing arrival times,
indexed from zero and tending to infinity, and let $w_i \ge 0$ be sojourn times. Customer $i$
is present at time $s$ if $a_i \le s < a_i + w_i$. Write $L(s)$ for the number present and $N$
for the number of arrivals by time $t \ge 0$. Then the integral of $L$ over $[0,t]$ is the sum
of $\min(w_i,t-a_i)$ over $i<N$. This area lies between the sum of sojourn times of customers
who have departed by $t$ and the sum of sojourn times of customers who have arrived by $t$.
No ordering of departure times is assumed.

Source: Karl Sigman, *Notes on Little's Law* (2009), equations (7)–(12). -/
lemma integral_queueOccupancy_eq_and_bounds {a w : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hma : Monotone a) (haTop : Tendsto a atTop atTop) (hw : ∀ i, 0 ≤ w i)
    {t : ℝ} (ht : 0 ≤ t) :
    let N := {i | a i ≤ t}.ncard
    let L := fun s : ℝ => ({i | a i ≤ s ∧ s < a i + w i}.ncard : ℝ)
    (∫ s in (0 : ℝ)..t, L s) = (∑ i ∈ Finset.range N, min (w i) (t - a i)) ∧
      (∑ i ∈ Finset.range N with a i + w i ≤ t, w i) ≤ (∫ s in (0 : ℝ)..t, L s) ∧
      (∫ s in (0 : ℝ)..t, L s) ≤ ∑ i ∈ Finset.range N, w i := by
  -- The arrivals by `t` form the prefix before the first arrival strictly after `t`.
  obtain ⟨j, hj⟩ := eventually_atTop.1 (tendsto_atTop.1 haTop (t + 1))
  have hex : ∃ i, t < a i := ⟨j, by linarith only [hj j le_rfl]⟩
  let n := Nat.find hex
  have hprefix (i : ℕ) : a i ≤ t ↔ i < n := by
    refine ⟨fun hi => lt_of_not_ge fun hni => ?_, fun hi => le_of_not_gt (Nat.find_min hex hi)⟩
    exact (not_lt_of_ge (hma hni |>.trans hi)) (Nat.find_spec hex)
  have hN : {i | a i ≤ t}.ncard = n := by
    have heq : {i | a i ≤ t} = (Finset.range n : Set ℕ) := by
      ext i
      simpa only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range] using hprefix i
    rw [heq, Set.ncard_coe_finset, Finset.card_range]
  dsimp only
  rw [hN]
  let L (s : ℝ) : ℝ := ({i | a i ≤ s ∧ s < a i + w i}.ncard : ℝ)
  let present (i : ℕ) : ℝ → ℝ := (Ico (a i) (a i + w i)).indicator (fun _ => 1)
  have hL (s : ℝ) (hs : s ≤ t) : L s = ∑ i ∈ Finset.range n, present i s := by
    have heq : {i | a i ≤ s ∧ s < a i + w i} =
        ((Finset.range n).filter (fun i => a i ≤ s ∧ s < a i + w i) : Set ℕ) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun hi => ⟨(hprefix i).mp (hi.1.trans hs), hi⟩, And.right⟩
    dsimp only [L]
    rw [heq, Set.ncard_coe_finset, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i _
    simp [present, Set.indicator, Set.mem_Ico]
  have hInt (i : ℕ) : IntervalIntegrable (present i) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ico_of_le ht).2
    have hfinite : volume (Ico (0 : ℝ) t) ≠ ⊤ := by
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
    exact (integrableOn_const hfinite : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 t))
      |>.indicator measurableSet_Ico
  have hOne (i : ℕ) (hi : i ∈ Finset.range n) :
      (∫ s in (0 : ℝ)..t, present i s) = min (w i) (t - a i) := by
    have hai : a i ≤ t := (hprefix i).2 (Finset.mem_range.mp hi)
    have hmin : a i ≤ min t (a i + w i) := le_min hai (le_add_of_nonneg_right (hw i))
    dsimp only [present]
    rw [intervalIntegral.integral_of_le ht, ← integral_Ico_eq_integral_Ioc,
      setIntegral_indicator measurableSet_Ico, Ico_inter_Ico, max_eq_right (ha i),
      setIntegral_const, Real.volume_real_Ico_of_le hmin, smul_eq_mul, mul_one,
      ← min_sub_sub_right, add_sub_cancel_left, min_comm]
  have hArea : (∫ s in (0 : ℝ)..t, L s) = ∑ i ∈ Finset.range n, min (w i) (t - a i) := by
    calc
      (∫ s in (0 : ℝ)..t, L s) = ∫ s in (0 : ℝ)..t, ∑ i ∈ Finset.range n, present i s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact hL s hs.2
      _ = ∑ i ∈ Finset.range n, min (w i) (t - a i) := by
        rw [intervalIntegral.integral_finsetSum (fun i _ => hInt i)]
        exact Finset.sum_congr rfl hOne
  change (∫ s in (0 : ℝ)..t, L s) = _ ∧ _ ≤ (∫ s in (0 : ℝ)..t, L s) ∧
    (∫ s in (0 : ℝ)..t, L s) ≤ _
  refine ⟨hArea, ?_, ?_⟩
  · rw [hArea, Finset.sum_filter]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hd : a i + w i ≤ t
    · rw [ite_eq_left hd, min_eq_left (by linarith only [hd])]
    · rw [ite_eq_right hd]
      exact le_min (hw i) (sub_nonneg.mpr ((hprefix i).2 (Finset.mem_range.mp hi)))
  · rw [hArea]
    exact Finset.sum_le_sum fun _ _ => min_le_left _ _

end

end MetaMathlibExt
