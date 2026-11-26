/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Throughput of a deterministic two-station serial line -/

open Finset

namespace MetaMathlibExt

private theorem sum_interval_lengths_le {d : ℕ} (a b : Fin d → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ t)
    (horder : ∀ ⦃j k⦄, j < k → b j ≤ a k) :
    (∑ j, (b j - a j)) ≤ t := by
  cases d with
  | zero => simpa using ht
  | succ d =>
    rw [sum_sub_distrib, Fin.sum_univ_castSucc b, Fin.sum_univ_succ a]
    have h : (∑ j : Fin d, b j.castSucc) ≤ ∑ j : Fin d, a j.succ :=
      sum_le_sum fun _ _ => horder Fin.castSucc_lt_succ
    linarith [ha 0, hb (Fin.last d)]

private theorem station_completions_le {d : ℕ} (a b : Fin d → ℝ) {μ : ℝ}
    (hμ : 0 < μ) (hb : ∀ j, 0 < b j) (hservice : ∀ j, 1 / μ ≤ b j - a j) :
    (d : ℝ) ≤ (∑ j, max 0 (-a j) / (b j - a j)) + μ * ∑ j, (b j - max 0 (a j)) := by
  rw [mul_sum, ← sum_add_distrib]
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using
    (sum_le_sum (s := (univ : Finset (Fin d))) (f := fun _ => (1 : ℝ)) fun j _ => by
      have hd : 0 < b j - a j := (one_div_pos.mpr hμ).trans_le (hservice j)
      have hclip : 0 ≤ b j - max 0 (a j) :=
        sub_nonneg.mpr (max_le (hb j).le (sub_pos.mp hd).le)
      have hsplit : max 0 (-a j) + (b j - max 0 (a j)) = b j - a j := by
        rcases le_total (a j) 0 with h | h
        · rw [max_eq_right (neg_nonneg.mpr h), max_eq_left h]
          ring
        · rw [max_eq_left (neg_nonpos.mpr h), max_eq_right h, zero_add]
      have hrate : 1 ≤ μ * (b j - a j) := by
        rw [mul_comm μ]
        exact (div_le_iff₀ hμ).mp (hservice j)
      calc
        (1 : ℝ) = (max 0 (-a j) + (b j - max 0 (a j))) / (b j - a j) := by
          rw [hsplit, div_self hd.ne']
        _ = max 0 (-a j) / (b j - a j) + (b j - max 0 (a j)) / (b j - a j) := add_div ..
        _ ≤ max 0 (-a j) / (b j - a j) + μ * (b j - max 0 (a j)) := by
          apply add_le_add_right
          apply (div_le_iff₀ hd).mpr
          calc
            b j - max 0 (a j) = (b j - max 0 (a j)) * 1 := (mul_one _).symm
            _ ≤ (b j - max 0 (a j)) * (μ * (b j - a j)) :=
              mul_le_mul_of_nonneg_left hrate hclip
            _ = μ * (b j - max 0 (a j)) * (b j - a j) := by ring)

private theorem initial_credit_le {d W : ℕ} (a b : Fin d → ℝ)
    (hb : ∀ j, 0 < b j) (hd : ∀ j, a j < b j)
    (horder : ∀ ⦃j k⦄, j < k → b j ≤ a k)
    (hinitial : ∀ j, a j < 0 → Nonempty (Fin W)) :
    (∑ j, max 0 (-a j) / (b j - a j)) ≤ W := by
  cases d with
  | zero => simp
  | succ d =>
    rw [Fin.sum_univ_succ]
    have htail : (∑ j : Fin d, max 0 (-a j.succ) / (b j.succ - a j.succ)) = 0 := by
      apply sum_eq_zero
      intro j _
      have h : 0 ≤ a j.succ := (hb 0).le.trans (horder (Fin.succ_pos j))
      rw [max_eq_left (neg_nonpos.mpr h), zero_div]
    rw [htail, add_zero]
    by_cases h : a 0 < 0
    · obtain ⟨k⟩ := hinitial 0 h
      calc
        max 0 (-a 0) / (b 0 - a 0) ≤ 1 := by
          apply (div_le_iff₀ (sub_pos.mpr (hd 0))).mpr
          rw [one_mul, max_eq_right (neg_nonneg.mpr h.le)]
          linarith [hb 0]
        _ ≤ (W : ℝ) := by exact_mod_cast (Nat.one_le_of_lt k.isLt)
    · rw [max_eq_left (neg_nonpos.mpr (le_of_not_gt h)), zero_div]
      exact Nat.cast_nonneg _

@[expose] public section

/-- **Throughput bound for a two-station serial line.** The stations are indexed by `0` and `1`
(upstream and downstream). For a window `(0, t]` with `t > 0`, `W` counts jobs present just
after time-zero events and `D` counts completions in the window. For each station, `start` and
`finish` give the full, nonoverlapping service intervals of its `D` completed jobs, in completion
order. Finish times lie in `(0, t]`; each duration is at least `1 / μ` for a positive rate `μ`.
An upstream job whose service starts at or before zero needs an initial upstream job. The
embedding `source` assigns each downstream completion a distinct initial downstream job or
in-window upstream completion, in the latter case no later than the downstream start.

The initial credit is the fraction already served before zero for the completed job, if any,
whose interval crosses zero. The completed-job busy time is the sum of the portions of these
intervals inside the window. Each station's completion count is at most its initial credit plus
its rate times its completed-job busy time. The downstream throughput is at most the smaller
rate plus the total initial job count divided by `t`.

The bottleneck-rate motivation is from Hopp and Spearman, *Factory Physics*, 3rd ed., Chapter 7;
the finite-window bound is derived here. -/
theorem two_station_throughput_bound {t : ℝ} (ht : 0 < t)
    (μ : Fin 2 → ℝ) (W D : Fin 2 → ℕ) (start finish : ∀ i, Fin (D i) → ℝ)
    (source : Fin (D 1) ↪ Fin (W 1) ⊕ Fin (D 0))
    (hμ : ∀ i, 0 < μ i) (hservice : ∀ i j, 1 / μ i ≤ finish i j - start i j)
    (hfinish : ∀ i j, 0 < finish i j ∧ finish i j ≤ t)
    (horder : ∀ i ⦃j k⦄, j < k → finish i j ≤ start i k)
    (hinitial : ∀ j, start 0 j ≤ 0 → Nonempty (Fin (W 0)))
    (hsource : ∀ j k, source j = Sum.inr k → finish 0 k ≤ start 1 j) :
    let credit (i : Fin 2) := ∑ j, max 0 (-start i j) / (finish i j - start i j)
    let busy (i : Fin 2) := ∑ j, (finish i j - max 0 (start i j))
    (∀ i : Fin 2, (D i : ℝ) ≤ credit i + μ i * busy i) ∧
      (D 1 : ℝ) / t ≤ min (μ 0) (μ 1) + ((W 0 : ℝ) + W 1) / t := by
  intro credit busy
  have hstation i := station_completions_le (start i) (finish i) (hμ i)
    (fun j => (hfinish i j).1) (hservice i)
  have hwindow i : busy i ≤ t :=
    sum_interval_lengths_le (fun j => max 0 (start i j)) (finish i) ht.le
      (fun _ => le_max_left _ _) (fun j => (hfinish i j).2)
      (by intro j k h; exact (horder i h).trans (le_max_right 0 (start i k)))
  have hhasInitial (i : Fin 2) (j : Fin (D i)) (hj : start i j < 0) :
      Nonempty (Fin (W i)) := by
    by_cases hi : i = 0
    · subst i
      exact hinitial j hj.le
    · obtain rfl := Fin.eq_one_of_ne_zero i hi
      cases hs : source j with
      | inl k => exact ⟨k⟩
      | inr k => exact ((hfinish 0 k).1.not_ge ((hsource j k hs).trans hj.le)).elim
  have hcredit (i : Fin 2) : credit i ≤ W i :=
    initial_credit_le (start i) (finish i) (fun j => (hfinish i j).1)
      (fun j => sub_pos.mp ((one_div_pos.mpr (hμ i)).trans_le (hservice i j)))
      (horder i) (hhasInitial i)
  have hcapacity (i : Fin 2) : (D i : ℝ) ≤ W i + μ i * t :=
    (hstation i).trans (add_le_add (hcredit i) (mul_le_mul_of_nonneg_left (hwindow i) (hμ i).le))
  have htransfer : D 1 ≤ W 1 + D 0 := by
    simpa using Fintype.card_le_of_embedding source
  have hflow : (D 1 : ℝ) ≤ (W 1 : ℝ) + D 0 := by exact_mod_cast htransfer
  have hupper (i : Fin 2) (hi : (D 1 : ℝ) ≤ μ i * t + ((W 0 : ℝ) + W 1)) :
      (D 1 : ℝ) / t ≤ μ i + ((W 0 : ℝ) + W 1) / t := by
    calc
      (D 1 : ℝ) / t ≤ (μ i * t + ((W 0 : ℝ) + W 1)) / t :=
        div_le_div_of_nonneg_right hi ht.le
      _ = μ i + ((W 0 : ℝ) + W 1) / t := by rw [add_div, mul_div_cancel_right₀ _ ht.ne']
  refine ⟨hstation, ?_⟩
  rcases le_total (μ 0) (μ 1) with h | h
  · rw [min_eq_left h]
    exact hupper 0 (by linarith [hflow, hcapacity 0])
  · rw [min_eq_right h]
    exact hupper 1 (by linarith [hcapacity 1, Nat.cast_nonneg (α := ℝ) (W 0)])

end

end MetaMathlibExt
