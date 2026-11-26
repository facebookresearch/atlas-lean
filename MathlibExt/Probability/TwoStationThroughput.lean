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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Throughput of a deterministic two-station serial line -/

open Finset

namespace MetaMathlibExt

private theorem station_completions_le {d : ℕ} (s : Fin d → ℝ) {μ β busy : ℝ}
    (hμ : 0 < μ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hs : ∀ j, 1 / μ ≤ s j)
    (hbusy : (∑ j : Fin d, (if j.val = 0 then 1 - β else 1) * s j) ≤ busy) :
    (d : ℝ) ≤ β + μ * busy := by
  let w (j : Fin d) : ℝ := if j.val = 0 then 1 - β else 1
  have hcount : (d : ℝ) - β ≤ ∑ j, w j := by
    dsimp only [w]
    cases d with
    | zero => simpa using hβ₀
    | succ d =>
      rw [Fin.sum_univ_succ]
      simp
      linarith
  have hwork : (∑ j, w j) ≤ μ * busy := by
    calc
      (∑ j, w j) ≤ ∑ j, μ * (w j * s j) := by
        apply sum_le_sum
        intro j _
        have hw : 0 ≤ w j := by
          dsimp only [w]
          split <;> linarith
        have hj : 1 ≤ μ * s j := by
          rw [mul_comm μ]
          exact (div_le_iff₀ hμ).mp (hs j)
        calc
          w j = w j * 1 := (mul_one _).symm
          _ ≤ w j * (μ * s j) := mul_le_mul_of_nonneg_left hj hw
          _ = μ * (w j * s j) := by ring
      _ = μ * ∑ j, w j * s j := (mul_sum _ _ _).symm
      _ ≤ μ * busy := mul_le_mul_of_nonneg_left hbusy hμ.le
  linarith

@[expose] public section

/-- **Throughput bound for a two-station serial line.** The stations are indexed by `0` and `1`
(upstream and downstream). Fix a window `(0, t]` with `t > 0`, rates `μ`, initial job counts `W`,
completion counts `D`, and in-window busy times `busy`. For each station, `s` lists the full
service requirements of its completed jobs in completion order. Each station has a strictly
positive rate `μ`, and its requirements are at least `1 / μ`. The first completion is credited
with a fraction `β` served before the window, if any;
`β` lies in `[0, 1]` and is bounded by the initial job count. The resulting sum of in-window
service requirements is at most `busy`, which is at most `t`. The downstream completions are
bounded by the initial downstream jobs plus upstream completions, counting the same window at
both stations. Then each `D i` is at most `β i + μ i * busy i`, and the downstream throughput
is at most `min (μ 0) (μ 1)` plus the total initial job count divided by `t`.

This is a deterministic bound on a fixed history. The bottleneck-rate motivation is from Hopp
and Spearman, *Factory Physics*, 3rd ed., Chapter 7; the finite-window bound is derived here. -/
theorem two_station_throughput_bound {t : ℝ} (ht : 0 < t)
    (μ β busy : Fin 2 → ℝ) (W D : Fin 2 → ℕ) (s : ∀ i, Fin (D i) → ℝ)
    (hμ : ∀ i, 0 < μ i) (hβ : ∀ i, 0 ≤ β i ∧ β i ≤ 1 ∧ β i ≤ W i)
    (hs : ∀ i j, 1 / μ i ≤ s i j)
    (hbusy : ∀ i, (∑ j : Fin (D i), (if j.val = 0 then 1 - β i else 1) * s i j) ≤ busy i)
    (hwindow : ∀ i, busy i ≤ t) (htransfer : D 1 ≤ W 1 + D 0) :
    (∀ i : Fin 2, (D i : ℝ) ≤ β i + μ i * busy i) ∧
      (D 1 : ℝ) / t ≤ min (μ 0) (μ 1) + ((W 0 : ℝ) + W 1) / t := by
  have hstation i := station_completions_le (s i) (hμ i) (hβ i).1 (hβ i).2.1 (hs i) (hbusy i)
  have hcapacity (i : Fin 2) : (D i : ℝ) ≤ W i + μ i * t :=
    (hstation i).trans (add_le_add (hβ i).2.2 (mul_le_mul_of_nonneg_left (hwindow i) (hμ i).le))
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
