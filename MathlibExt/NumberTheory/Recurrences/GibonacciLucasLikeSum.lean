/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Fib.Basic
import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # A two-sequence gibonacci identity with Lucas-type sums -/

namespace MetaMathlibExt

/-- **Two-sequence gibonacci identity with a Fibonacci factor and Lucas-type sums.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$, $k$ and $s$,
$$
G_s (H_{r+k+1} + H_{r+k-1}) + (-1)^{r-1} G_{s-r} (H_{k+1} + H_{k-1}) =
G_0 F_r (H_{k+s} + H_{k+s-2}) + G_1 F_r (H_{k+s+1} + H_{k+s-1}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 40
(`jis-2024-24.6.2-prop-40`). -/
public theorem gibonacci_lucas_like_mul_add_eq_fib_mul
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r k s : ℤ) :
    G s * (H (r + k + 1) + H (r + k - 1)) +
        (-1 : ℝ) ^ (r - 1) * G (s - r) * (H (k + 1) + H (k - 1)) =
      G 0 * (Int.fib r : ℝ) * (H (k + s) + H (k + s - 2)) +
        G 1 * (Int.fib r : ℝ) * (H (k + s + 1) + H (k + s - 1)) := by
  -- The shifts by +1 and -1 pair the neighbors of each index in H.
  linear_combination (norm := ring1_nf)
    gibonacci_mul_add_neg_one_pow_eq_fib_mul G H hG hH r (r + k + 1) (s - r) +
    gibonacci_mul_add_neg_one_pow_eq_fib_mul G H hG hH r (r + k - 1) (s - r)

end MetaMathlibExt
