/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity

/-! # Catalan-type identity for Fibonacci and gibonacci numbers -/

namespace MetaMathlibExt

private theorem fib_catalan_zpow (k r : ℤ) :
    (Int.fib (k + r) : ℝ) * Int.fib (k - r) - (Int.fib k : ℝ) ^ 2 =
      (-1 : ℝ) ^ (k + r + 1) * (Int.fib r : ℝ) ^ 2 := by
  have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (k - r) r
  rw [sub_add_cancel, show k - r + 2 * r = k + r by omega, mul_comm (Int.fib (k - r))] at h
  have hcast : (Int.fib k : ℝ) ^ 2 - (Int.fib (k + r) : ℝ) * Int.fib (k - r) =
      (-1 : ℝ) ^ (k - r).natAbs * (Int.fib r : ℝ) ^ 2 := by
    exact_mod_cast h
  have habs : (-1 : ℝ) ^ (k - r).natAbs = (-1 : ℝ) ^ (k - r) := by
    rw [← zpow_natCast]
    obtain ⟨n, hn | hn⟩ := (k - r).eq_nat_or_neg
    · rw [hn, Int.natAbs_natCast]
    · rw [hn, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow]
      norm_num
  have hsign : (-1 : ℝ) ^ (k + r) = (-1 : ℝ) ^ (k - r) := by
    rw [show k + r = k - r + 2 * r by omega, zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  rw [habs, ← hsign] at hcast
  rw [zpow_add_one₀ (by norm_num)]
  linear_combination -hcast

/-- **Catalan-type identity for Fibonacci and gibonacci numbers.** Let $F_m$ denote the Fibonacci
numbers, extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$. If
$G : \mathbb{Z} \to \mathbb{R}$ satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
for all integers $k$, $r$ and $s$,
$$
F_{k+r} G_{k-r+s} + F_{k-r} G_{k+r+s}
= 2 F_k G_{k+s} + (-1)^{k+r+1} F_r^2 \left(G_{s+1} + G_{s-1}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 43
(`jis-2024-24.6.2-prop-43`). -/
public theorem fib_gibonacci_catalan_type_identity
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k r s : ℤ) :
    (Int.fib (k + r) : ℝ) * G (k - r + s) + (Int.fib (k - r) : ℝ) * G (k + r + s) =
      2 * (Int.fib k : ℝ) * G (k + s) +
        (-1 : ℝ) ^ (k + r + 1) * (Int.fib r : ℝ) ^ 2 * (G (s + 1) + G (s - 1)) := by
  have shift (n : ℤ) :
      G (n + s) = (Int.fib (n + 1) : ℝ) * G s + (Int.fib n : ℝ) * G (s - 1) := by
    simpa only [sub_add_cancel, show n + (s - 1) + 1 = n + s by omega] using
      (fib_mul_gibonacci_add_eq_gibonacci G hG n (s - 1)).symm
  have h₀ := fib_catalan_zpow k r
  have h₁ := fib_catalan_zpow (k + 1) r
  have h₂ := fib_catalan_zpow (k + 2) r
  -- Expanding the Catalan difference at k + 2 produces the mixed coefficient in the shift formula.
  rw [show k + 1 + r = k + r + 1 by omega, show k + 1 - r = k - r + 1 by omega,
    zpow_add_one₀ (by norm_num)] at h₁
  rw [show k + 2 + r + 1 = (k + r + 1) + 2 by omega, zpow_add₀ (by norm_num),
    show (-1 : ℝ) ^ (2 : ℤ) = 1 by norm_num, mul_one,
    show k + 2 + r = k + r + 2 by omega, show k + 2 - r = k - r + 2 by omega] at h₂
  simp only [Int.fib_add_two, Int.cast_add] at h₂
  have hcross : (Int.fib (k + r) : ℝ) * Int.fib (k - r + 1) +
      (Int.fib (k - r) : ℝ) * Int.fib (k + r + 1) - 2 * (Int.fib k : ℝ) * Int.fib (k + 1) =
        (-1 : ℝ) ^ (k + r + 1) * (Int.fib r : ℝ) ^ 2 := by
    linear_combination h₂ - h₁ - h₀
  have hstep : G (s + 1) = G s + G (s - 1) := by
    simpa only [sub_add_cancel, show s - 1 + 2 = s + 1 by omega] using hG (s - 1)
  rw [shift (k - r), shift (k + r), shift k, hstep]
  linear_combination G s * hcross + 2 * G (s - 1) * h₀

end MetaMathlibExt
