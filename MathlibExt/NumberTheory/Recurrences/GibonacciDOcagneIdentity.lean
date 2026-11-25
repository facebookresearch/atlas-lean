/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # d'Ocagne-type identity for two gibonacci sequences -/

namespace MetaMathlibExt

/-- **d'Ocagne-type identity for two gibonacci sequences.** Let $G$ and $H$ be gibonacci
sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with $X_{j+2} = X_{j+1} + X_j$
for every integer $j$. Then for all integers $r$, $s$, $k$,

$$
H_{r+s} G_{k+1} - H_{r+s+1} G_k =
(-1)^{r-1} (H_{s+1} + H_{s-1}) G_{k-r} + (-1)^r (G_0 H_{k+s-r-1} + G_1 H_{k+s-r}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 23
(`jis-2024-24.6.2-prop-23`). -/
public theorem gibonacci_dOcagne_type_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r s k : ℤ) :
    H (r + s) * G (k + 1) - H (r + s + 1) * G k =
      (-1 : ℝ) ^ (r - 1) * (H (s + 1) + H (s - 1)) * G (k - r) +
        (-1 : ℝ) ^ r * (G 0 * H (k + s - r - 1) + G 1 * H (k + s - r)) := by
  -- The two shifted product identities have the same Fibonacci-weighted right side.
  have h₁ := gibonacci_mul_add_neg_one_pow_eq_fib_mul H G hH hG r (k + 1) s
  have h₂ := gibonacci_mul_add_neg_one_pow_eq_fib_mul H G hH hG r k (s + 1)
  have hseed := gibonacci_mul_gibonacci_add_eq_seed_combination G H hG hH (s - 1) (k - r)
  have hsign : (-1 : ℝ) ^ (r - 1) = -(-1 : ℝ) ^ r := by
    simp [zpow_sub_one₀]
  linear_combination (norm := (simp only [hsign]; ring1_nf)) h₁ - h₂ + (-1 : ℝ) ^ r * hseed

end MetaMathlibExt
