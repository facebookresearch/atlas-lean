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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A Fibonacci–Lucas identity for gibonacci sequences

The two-sequence Fibonacci-factor identity specialized to signed Fibonacci numbers gives the
Cassini factor. The gibonacci addition law then reduces the desired identity to that factor.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **A Fibonacci–Lucas identity for gibonacci sequences.** Let $F_m$ denote the Fibonacci
numbers, extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$, and let
$L_m = F_{m-1} + F_{m+1}$ be the Lucas numbers, for every integer $m$. If
$G : \mathbb{Z} \to \mathbb{R}$ satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
for all integers $k$ and $r$,
$$
5 F_k G_{k+r} - L_k \left(G_{k+r+1} + G_{k+r-1}\right)
= 2 (-1)^{k-1} \left(G_{r+1} + G_{r-1}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 18
(`jis-2024-24.6.2-prop-18`). -/
public theorem five_fib_mul_gibonacci_sub_lucas_mul
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k r : ℤ) :
    5 * (Int.fib k : ℝ) * G (k + r) - L k * (G (k + r + 1) + G (k + r - 1)) =
      (-1 : ℝ) ^ (k - 1) * 2 * (G (r + 1) + G (r - 1)) := by
  let F : ℤ → ℝ := fun j => Int.fib j
  have hF (j : ℤ) : F (j + 2) = F (j + 1) + F j := by
    simpa only [F, Int.cast_add] using congrArg (fun a : ℤ => (a : ℝ))
      ((Int.fib_add_two j).trans (add_comm _ _))
  have hF0 : F 0 = 0 := by norm_num [F]
  have hF1 : F 1 = 1 := by norm_num [F]
  have hFneg : F (-1) = 1 := by norm_num [F]
  have hCassini : F k ^ 2 - F (k + 1) * F (k - 1) = (-1 : ℝ) ^ (k - 1) := by
    have h := gibonacci_mul_add_neg_one_pow_eq_fib_mul F F hF hF k (k + 1) (-1)
    rw [show (-1 : ℤ) + k = k - 1 by ring, show k + 1 - k = 1 by ring,
      show (-1 : ℤ) + (k + 1) = k by ring] at h
    simp only [hF0, hF1, hFneg, zero_mul, one_mul, zero_add, mul_one] at h
    nlinarith only [h]
  have hFnext : F (k + 1) = F k + F (k - 1) := by
    simpa only [show k - 1 + 2 = k + 1 by ring, show k - 1 + 1 = k by ring] using hF (k - 1)
  have hprev (j : ℤ) : G (j - 1) = G (j + 1) - G j := by
    have h := hG (j - 1)
    rw [show j - 1 + 2 = j + 1 by ring, show j - 1 + 1 = j by ring] at h
    linarith only [h]
  have hGbase : G (k + r) = F k * G (r + 1) + F (k - 1) * G r := by
    simpa only [show k - 1 + 1 = k by ring, show k - 1 + r + 1 = k + r by ring] using
      (fib_mul_gibonacci_add_eq_gibonacci G hG (k - 1) r).symm
  have hGnext : G (k + r + 1) = F (k + 1) * G (r + 1) + F k * G r :=
    (fib_mul_gibonacci_add_eq_gibonacci G hG k r).symm
  have hLk : L k = F (k - 1) + F (k + 1) := hL k
  change 5 * F k * G (k + r) - L k * (G (k + r + 1) + G (k + r - 1)) = _
  calc
    _ = (F k ^ 2 - F (k + 1) * F (k - 1)) * 2 * (G (r + 1) + G (r - 1)) := by
      rw [hLk, hprev (k + r), hGbase, hGnext, hprev r, hFnext]
      ring
    _ = _ := by rw [hCassini]

end

end MetaMathlibExt
