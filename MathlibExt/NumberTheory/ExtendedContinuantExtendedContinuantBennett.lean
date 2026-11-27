/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Tactic.Ring

/-!
# Bennett's identity for extended continuants

This module proves Bennett's continuant identity for all integer indices.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 3.
-/

namespace MetaMathlibExt

private theorem extendedContinuant_eq_det (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x (b - a - 2) a =
      (b.negOnePow : ℤ) *
        (extendedContinuant x (-a - 2) a * extendedContinuant x (-b - 1) b -
          extendedContinuant x (-a - 1) a * extendedContinuant x (-b - 2) b) := by
  let K (c t : ℤ) := extendedContinuant x (t - c - 2) c
  have recurrence (c t : ℤ) : K c (t + 2) = x t * K c (t + 1) + K c t := by
    dsimp only [K]
    convert extendedContinuant_recurrence x (t + 2 - c - 2) c using 1
    ring_nf
  let D (t : ℤ) := K a t * K b (t + 1) - K a (t + 1) * K b t
  have flip (t : ℤ) : D (t + 1) = -D t := by
    dsimp only [D]
    rw [show t + 1 + 1 = t + 2 by ring, recurrence a t, recurrence b t]
    ring
  let P (t : ℤ) := D t = ((t - b).negOnePow : ℤ) * K a b
  have step (t : ℤ) : P (t + 1) ↔ P t := by
    dsimp only [P]
    rw [show t + 1 - b = (t - b) + 1 by ring, flip, Int.negOnePow_succ,
      Units.val_neg, neg_mul, neg_inj]
  have base : P b := by
    dsimp only [P, D, K]
    ring_nf
    simp [extendedContinuant_neg_two, extendedContinuant_neg_one]
  have h₀ : P 0 := Int.inductionOn' 0 b base (fun t _ => (step t).2)
    (fun t _ ih => (step (t - 1)).1 (by simpa only [sub_add_cancel] using ih))
  simp only [P, zero_sub, Int.negOnePow_neg] at h₀
  have h : K a b = (b.negOnePow : ℤ) * D 0 := by
    rw [h₀, ← mul_assoc, Int.units_coe_mul_self, one_mul]
  convert h using 1
  dsimp only [K, D]
  ring_nf

/-- **Bennett's continuant identity for all integer indices.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all integers $k$, $\ell$, $m$, $n$,
$$(-1)^{k+\ell} K_{n-k-2}(x)_k K_{m-\ell-2}(x)_\ell +
(-1)^{\ell+m} K_{n-\ell-2}(x)_\ell K_{k-m-2}(x)_m +
(-1)^{m+k} K_{n-m-2}(x)_m K_{\ell-k-2}(x)_k = 0.$$

This extends Bennett's identity from nonnegative to arbitrary integer indices.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 3. -/
public theorem extendedContinuant_bennett (x : ℤ → ℤ) (k ℓ m n : ℤ) :
    ((k + ℓ).negOnePow : ℤ) * extendedContinuant x (n - k - 2) k *
        extendedContinuant x (m - ℓ - 2) ℓ +
      ((ℓ + m).negOnePow : ℤ) * extendedContinuant x (n - ℓ - 2) ℓ *
        extendedContinuant x (k - m - 2) m +
      ((m + k).negOnePow : ℤ) * extendedContinuant x (n - m - 2) m *
        extendedContinuant x (ℓ - k - 2) k = 0 := by
  rw [extendedContinuant_eq_det x k n, extendedContinuant_eq_det x ℓ m,
    extendedContinuant_eq_det x ℓ n, extendedContinuant_eq_det x m k,
    extendedContinuant_eq_det x m n, extendedContinuant_eq_det x k ℓ]
  simp only [Int.negOnePow_add, Units.val_mul]
  ring

end MetaMathlibExt
