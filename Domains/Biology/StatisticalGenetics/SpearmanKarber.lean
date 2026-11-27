/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Finite summation by parts for the Spearman–Kärber value -/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted

open Finset

/-- The Spearman–Kärber value `∑ᵢ (pᵢ₊₁ - pᵢ) (xᵢ + xᵢ₊₁) / 2` for doses `xᵢ = x₀ + i d`,
`i = 0, …, k`, and response proportions `p`; for nondecreasing `p` with `p₀ = 0` and `p_k = 1` it
is the mean of the distribution with mass `pᵢ₊₁ - pᵢ` at `(xᵢ + xᵢ₊₁) / 2`. -/
noncomputable def spearmanKarber (x₀ d : ℝ) {k : ℕ} (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ i : Fin k, (p i.succ - p i.castSucc) *
    ((x₀ + (i : ℕ) * d) + (x₀ + ((i : ℕ) + 1) * d)) / 2

/-- **Summation by parts** (Irwin and Cheeseman 1939, p. 574): for doses `xᵢ = x₀ + i d`,
`i = 0, …, k` with `k ≥ 1`, and any proportions `p` with `p₀ = 0` and `p_k = 1`, the
Spearman–Kärber value equals `x_k - d (½ p₀ + p₁ + ⋯ + p_{k-1} + ½ p_k)`.

Source: Irwin and Cheeseman (1939), p. 574. -/
theorem spearmanKarber_eq (x₀ d : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : Fin (k + 1) → ℝ)
    (h₀ : p 0 = 0) (hk₁ : p (Fin.last k) = 1) :
    spearmanKarber x₀ d p =
      (x₀ + k * d) - d * (p 0 / 2 + ∑ i : Fin (k + 1), (if i = 0 ∨ i = Fin.last k then 0 else p i) +
        p (Fin.last k) / 2) := by
  cases k with
  | zero => exact (Nat.not_succ_le_zero 0 hk).elim
  | succ n =>
    -- Align the two shifted sums on the interior indices; only their endpoint terms differ.
    let w (i : ℕ) : ℝ := x₀ + i * d + d / 2
    have hpos : (∑ i : Fin (n + 1), p i.succ * w i) =
        (∑ i : Fin n, p i.castSucc.succ * w i) + p (Fin.last (n + 1)) * w n := by
      simpa only [Fin.val_castSucc, Fin.succ_last, Fin.val_last] using
        (Fin.sum_univ_castSucc fun i : Fin (n + 1) => p i.succ * w i)
    have hneg : (∑ i : Fin (n + 1), p i.castSucc * w i) =
        p 0 * w 0 + ∑ i : Fin n, p i.castSucc.succ * w (i.succ : ℕ) := by
      simpa only [Fin.val_castSucc, Fin.castSucc_succ, Fin.val_zero, Fin.castSucc_zero] using
        (Fin.sum_univ_succ fun i : Fin (n + 1) => p i.castSucc * w i)
    -- Consecutive midpoint weights differ by d.
    have hmid : (∑ i : Fin n, p i.castSucc.succ * w i) -
        (∑ i : Fin n, p i.castSucc.succ * w (i.succ : ℕ)) =
        -d * ∑ i : Fin n, p i.castSucc.succ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
    let q (i : Fin (n + 2)) : ℝ := if i = 0 ∨ i = Fin.last (n + 1) then 0 else p i
    have hq : (∑ i, q i) = ∑ i : Fin n, p i.castSucc.succ := by
      have hfirst : q 0 = 0 := by simp [q]
      have hlast : q (Fin.last (n + 1)) = 0 := by simp [q]
      have hinterior (i : Fin n) : q i.castSucc.succ = p i.castSucc.succ := by
        have hi : i.castSucc.succ ≠ Fin.last (n + 1) := by
          rw [Fin.succ_castSucc]
          exact Fin.castSucc_ne_last _
        exact ite_eq_right (not_or.mpr ⟨Fin.succ_ne_zero _, hi⟩)
      rw [Fin.sum_univ_succ, hfirst, zero_add, Fin.sum_univ_castSucc]
      simp only [Fin.succ_last, hlast, add_zero, hinterior]
    change spearmanKarber x₀ d p =
      (x₀ + (n + 1 : ℕ) * d) - d * (p 0 / 2 + (∑ i, q i) + p (Fin.last (n + 1)) / 2)
    calc
      spearmanKarber x₀ d p = ∑ i : Fin (n + 1), (p i.succ - p i.castSucc) * w i := by
        unfold spearmanKarber
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [w]
        ring
      _ = (∑ i : Fin (n + 1), p i.succ * w i) - ∑ i : Fin (n + 1), p i.castSucc * w i := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      _ = p (Fin.last (n + 1)) * w n - p 0 * w 0 +
          ((∑ i : Fin n, p i.castSucc.succ * w i) -
            ∑ i : Fin n, p i.castSucc.succ * w (i.succ : ℕ)) := by
        rw [hpos, hneg]
        ring
      _ = _ := by
        rw [hmid, ← hq, h₀, hk₁]
        simp only [w, Nat.cast_add, Nat.cast_one]
        ring

end WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted
