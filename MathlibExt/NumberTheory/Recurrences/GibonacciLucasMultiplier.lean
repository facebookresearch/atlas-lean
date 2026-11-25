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

/-! # Lucas multiplier identity for gibonacci sequences -/

namespace MetaMathlibExt

/-- **Lucas multiplier identity for gibonacci sequences.** Let $F_m$ be the Fibonacci numbers,
extended to all integers $m$ by $F_{m+2} = F_{m+1} + F_m$, and let $L_m = F_{m-1} + F_{m+1}$ be
the Lucas numbers. Let $G : \mathbb{Z} \to \mathbb{R}$ be a gibonacci sequence, that is,
$G_{j+2} = G_{j+1} + G_j$ for every integer $j$. Then for all integers $r$ and $s$,
$G_{s+r} + (-1)^r G_{s-r} = L_r G_s$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 39
(`jis-2024-24.6.2-prop-39`). -/
public theorem gibonacci_add_neg_one_pow_mul_eq_lucas_mul
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (r s : ℤ) :
    G (s + r) + (-1 : ℝ) ^ r * G (s - r) = L r * G s := by
  have hfib (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
    rw [Int.fib_add_two, Int.cast_add, add_comm]
  -- Expand the forward shift and express the signed backward shift using the same two terms.
  have hforward := fib_mul_gibonacci_add_eq_gibonacci G hG (r - 1) s
  have hback := gibonacci_mul_add_neg_one_pow_eq_fib_mul (fun j => (Int.fib j : ℝ)) G
    hfib hG r s 1
  simp only [sub_add_cancel, show r - 1 + s + 1 = s + r by omega] at hforward
  simp [add_comm (1 : ℤ), zpow_sub_one₀] at hback
  rw [hL]
  linear_combination -hforward - hback

end MetaMathlibExt
