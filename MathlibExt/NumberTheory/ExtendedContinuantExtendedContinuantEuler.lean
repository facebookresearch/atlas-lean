/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Euler's identity for extended continuants

Euler's continuant identity holds for arbitrary integer orders and start indices.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 1.
-/

namespace MetaMathlibExt

private theorem zero_of_recurrence (f c : ℤ → ℤ) (b n : ℤ)
    (hrec : ∀ t, f (t + 2) = c t * f (t + 1) + f t)
    (h₀ : f b = 0) (h₁ : f (b + 1) = 0) : f n = 0 := by
  have pair : ∀ t, f t = 0 ∧ f (t + 1) = 0 := by
    intro t
    refine Int.inductionOn' t b ⟨h₀, h₁⟩ (fun t _ ih => ?_) (fun t _ ih => ?_)
    · refine ⟨ih.2, ?_⟩
      rw [show t + 1 + 1 = t + 2 by ring, hrec, ih.1, ih.2]
      ring
    · refine ⟨?_, by simpa using ih.1⟩
      have h := hrec (t - 1)
      rw [show t - 1 + 2 = t + 1 by ring, sub_add_cancel, ih.1, ih.2] at h
      linear_combination -h
  exact (pair n).1

private theorem extendedContinuant_euler_adjacent (x : ℤ → ℤ) (h k ℓ : ℤ) :
    extendedContinuant x (ℓ + k + 1) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
        extendedContinuant x k (ℓ + h + 1) * extendedContinuant x (k + ℓ) h =
      (k.negOnePow : ℤ) * extendedContinuant x (ℓ - 1) h := by
  let K (b t : ℤ) := extendedContinuant x (t - b) b
  have recurrence (b t : ℤ) :
      K b (t + 2) = x (t + 2) * K b (t + 1) + K b t := by
    dsimp only [K]
    convert extendedContinuant_recurrence x (t + 2 - b) b using 1
    ring_nf
  let b := ℓ + h + 1
  let D (t : ℤ) := K h (t + 1) * K b t - K b (t + 1) * K h t
  have flip (t : ℤ) : D (t + 1) = -D t := by
    dsimp only [D]
    rw [show t + 1 + 1 = t + 2 by ring, recurrence h t, recurrence b t]
    ring
  let P (t : ℤ) := D (ℓ + h + t) = (t.negOnePow : ℤ) * extendedContinuant x (ℓ - 1) h
  have step (t : ℤ) : P (t + 1) ↔ P t := by
    simp only [P, show ℓ + h + (t + 1) = ℓ + h + t + 1 by ring, flip,
      Int.negOnePow_succ, Units.val_neg, neg_mul, neg_inj]
  have base : P 0 := by
    dsimp only [P, D, K, b]
    simp only [Int.negOnePow_zero, Units.val_one, one_mul, add_zero]
    ring_nf
    rw [extendedContinuant_neg_one, extendedContinuant_zero]
    have r := extendedContinuant_recurrence x (ℓ + 1) h
    ring_nf at r ⊢
    linear_combination r
  have hk : P k := Int.inductionOn' k 0 base (fun t _ => (step t).2)
    (fun t _ ih => (step (t - 1)).1 (by simpa using ih))
  dsimp only [P, D, K, b] at hk
  convert hk using 1
  ring_nf

/-- **Euler's continuant identity for extended continuants.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all integers $h$, $k$, $\ell$, $m$,
$$K_{\ell+m}(x)_h K_{k-1}(x)_{\ell+h+1} - K_{m-1}(x)_{\ell+h+1} K_{k+\ell}(x)_h =
(-1)^k K_{m-k-2}(x)_{k+\ell+h+2} K_{\ell-1}(x)_h.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Corollary 1. -/
public theorem extendedContinuant_euler (x : ℤ → ℤ) (h k ℓ m : ℤ) :
    extendedContinuant x (ℓ + m) h * extendedContinuant x (k - 1) (ℓ + h + 1) -
        extendedContinuant x (m - 1) (ℓ + h + 1) * extendedContinuant x (k + ℓ) h =
      (k.negOnePow : ℤ) * extendedContinuant x (m - k - 2) (k + ℓ + h + 2) *
        extendedContinuant x (ℓ - 1) h := by
  let a := extendedContinuant x (k - 1) (ℓ + h + 1)
  let b := extendedContinuant x (k + ℓ) h
  let d := (k.negOnePow : ℤ) * extendedContinuant x (ℓ - 1) h
  let F (t : ℤ) := extendedContinuant x (ℓ + t) h * a -
    extendedContinuant x (t - 1) (ℓ + h + 1) * b -
    extendedContinuant x (t - k - 2) (k + ℓ + h + 2) * d
  have recurrence (t : ℤ) :
      F (t + 2) = x (ℓ + h + t + 2) * F (t + 1) + F t := by
    have r₀ := extendedContinuant_recurrence x (ℓ + t + 2) h
    have r₁ := extendedContinuant_recurrence x (t + 1) (ℓ + h + 1)
    have r₂ := extendedContinuant_recurrence x (t - k) (k + ℓ + h + 2)
    dsimp only [F]
    ring_nf at r₀ r₁ r₂ ⊢
    linear_combination a * r₀ - b * r₁ - d * r₂
  have h₀ : F k = 0 := by
    dsimp only [F, a, b]
    rw [show k - k - 2 = -2 by ring, extendedContinuant_neg_two]
    ring_nf
  have h₁ : F (k + 1) = 0 := by
    dsimp only [F, a, b, d]
    rw [show k + 1 - 1 = k by ring, show k + 1 - k - 2 = -1 by ring,
      extendedContinuant_neg_one, one_mul]
    have hadj := extendedContinuant_euler_adjacent x h k ℓ
    ring_nf at hadj ⊢
    linear_combination hadj
  have hm := zero_of_recurrence F (fun t => x (ℓ + h + t + 2)) k m recurrence h₀ h₁
  dsimp only [F, a, b, d] at hm
  linear_combination hm

end MetaMathlibExt
