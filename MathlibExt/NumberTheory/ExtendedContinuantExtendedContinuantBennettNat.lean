/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantEuler
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
  have h := extendedContinuant_euler x 0 (k - 2) 0 (n - 2)
  rw [zero_sub, extendedContinuant_neg_one, mul_one, Int.negOnePow_sub,
    Int.negOnePow_even 2 even_two, mul_one] at h
  convert h.symm using 2 <;> ring_nf

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
