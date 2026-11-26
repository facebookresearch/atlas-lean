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
# Bennett's continuant identity for nonnegative indices

This module proves Bennett's identity for extended continuants at nonnegative indices.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett, 1939).
-/

namespace MetaMathlibExt

@[expose] public section

private theorem continuant_minor (x : ℤ → ℤ) (k n : ℤ) :
    (k.negOnePow : ℤ) * extendedContinuant x (n - k - 2) k =
      extendedContinuant x (n - 2) 0 * extendedContinuant x (k - 3) 1 -
        extendedContinuant x (n - 3) 1 * extendedContinuant x (k - 2) 0 := by
  let C (b t : ℤ) := extendedContinuant x (t - b - 2) b
  have recurrence (b t : ℤ) : C b (t + 2) = x t * C b (t + 1) + C b t := by
    dsimp only [C]
    convert extendedContinuant_recurrence x (t - b) b using 1 <;> ring_nf
  let E (t : ℤ) := (k.negOnePow : ℤ) * C k t -
    (C 0 t * C 1 k - C 1 t * C 0 k)
  have step (t : ℤ) : E (t + 2) = x t * E (t + 1) + E t := by
    dsimp only [E]
    rw [recurrence k t, recurrence 0 t, recurrence 1 t]
    ring
  have base : E k = 0 ∧ E (k + 1) = 0 := by
    constructor
    · simp [E, C, extendedContinuant_neg_two]
      ring
    · have h := extendedContinuant_det x (k - 1)
      dsimp only [E, C]
      rw [show k + 1 - k - 2 = -1 by ring, extendedContinuant_neg_one, mul_one]
      convert sub_eq_zero.mpr h.symm using 1; ring_nf
  have hn : E n = 0 ∧ E (n + 1) = 0 := by
    refine Int.inductionOn' n k base (fun t _ ih => ?_) (fun t _ ih => ?_)
    · refine ⟨ih.2, ?_⟩
      simpa [show t + 1 + 1 = t + 2 by ring, ih.1, ih.2] using step t
    · constructor
      · have h := step (t - 1)
        simpa [show t - 1 + 2 = t + 1 by ring, ih.1, ih.2] using h.symm
      · simpa using ih.1
  have h := sub_eq_zero.mp hn.1
  simpa [E, C, sub_zero, show n - 1 - 2 = n - 3 by ring,
    show k - 1 - 2 = k - 3 by ring] using h

/-- **Bennett's continuant identity for nonnegative indices.** Let $x : \mathbb{Z} \to \mathbb{Z}$
be an integer sequence and write $K_a(x)_b$ for its extended continuant of order $a$ with start
index $b$. For all nonnegative integers $k$, $\ell$, $m$, $n$,
$$(-1)^{k+\ell} K_{n-k-2}(x)_k K_{m-\ell-2}(x)_\ell +
(-1)^{\ell+m} K_{n-\ell-2}(x)_\ell K_{k-m-2}(x)_m +
(-1)^{m+k} K_{n-m-2}(x)_m K_{\ell-k-2}(x)_k = 0.$$

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 2 (after G. T. Bennett, 1939). -/
public theorem extendedContinuant_bennett_nat (x : ℤ → ℤ) (k ℓ m n : ℕ) :
    ((k + ℓ : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - k - 2) k *
        extendedContinuant x ((m : ℤ) - ℓ - 2) ℓ +
      ((ℓ + m : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - ℓ - 2) ℓ *
        extendedContinuant x ((k : ℤ) - m - 2) m +
      ((m + k : ℤ).negOnePow : ℤ) * extendedContinuant x ((n : ℤ) - m - 2) m *
        extendedContinuant x ((ℓ : ℤ) - k - 2) k = 0
    := by
  simp only [Int.negOnePow_add, Units.val_mul]
  have regroup (a b u v : ℤ) : (a * b) * u * v = (a * u) * (b * v) := by ring
  simp only [regroup, continuant_minor]
  ring

end

end MetaMathlibExt
