/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity

/-!
# Gibonacci index doubling

Applying the gibonacci addition formula twice reduces index doubling to the recurrences for
signed Fibonacci numbers and for the gibonacci sequence.
-/

namespace MetaMathlibExt

/-- **Gibonacci index doubling via Fibonacci squares.** Let $F_m$ be the Fibonacci numbers
extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$), and let
$G \colon \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$.
Then for all integers $k$, $s$,
$$G_{2k+s} = F_{k+1}^2 G_{s+1} + F_k^2 G_s - F_{k-1}^2 G_{s-1}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 26
(`jis-2024-24.6.2-prop-26`). -/
public theorem gibonacci_two_mul_add_eq_fib_sq_combination
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k s : ℤ) :
    G (2 * k + s) = (Int.fib (k + 1) : ℝ) ^ 2 * G (s + 1) + (Int.fib k : ℝ) ^ 2 * G s -
      (Int.fib (k - 1) : ℝ) ^ 2 * G (s - 1) := by
  have hdouble := fib_mul_gibonacci_add_eq_gibonacci G hG k (k + s - 1)
  simp only [show k + (k + s - 1) + 1 = 2 * k + s by ring, sub_add_cancel] at hdouble
  have hshift (t : ℤ) : G (k + t) =
      (Int.fib k : ℝ) * G (t + 1) + (Int.fib (k - 1) : ℝ) * G t := by
    simpa only [show k - 1 + t + 1 = k + t by ring, sub_add_cancel] using
      (fib_mul_gibonacci_add_eq_gibonacci G hG (k - 1) t).symm
  have hF : (Int.fib (k + 1) : ℝ) = Int.fib (k - 1) + Int.fib k := by
    simpa only [show k - 1 + 2 = k + 1 by ring, sub_add_cancel, Int.cast_add] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.fib_add_two (k - 1))
  have hGnext : G (s + 1) = G s + G (s - 1) := by
    simpa only [show s - 1 + 2 = s + 1 by ring, sub_add_cancel] using hG (s - 1)
  rw [← hdouble, hshift s, show k + s - 1 = k + (s - 1) by ring, hshift (s - 1),
    sub_add_cancel, hF, hGnext]
  ring

end MetaMathlibExt
