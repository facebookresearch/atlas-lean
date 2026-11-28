/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Odd-indexed Fibonacci numbers times the golden ratio

Binet's formula gives `F_{n+1} - φ F_n = ψ ^ n` with `ψ = (1 - √5)/2`
(`Real.fib_succ_sub_goldenRatio_mul_fib`), so `F_n φ = F_{n+1} + (-ψ) ^ n` for odd `n`. Since
`-ψ = (√5 - 1)/2`, this is `F_{2k+1} φ = F_{2k+2} + ((√5 - 1)/2) ^ (2k+1)`. Adding `F_{2k+1}`
and using `F_{2k+3} = F_{2k+1} + F_{2k+2}` gives the same error term for `1 + φ`.
-/

namespace MetaMathlibExt

/-- **Odd-indexed Fibonacci numbers times the golden ratio.** Let $F_n$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{n+2} = F_{n+1} + F_n$) and $\varphi = (1 + \sqrt 5)/2$ the golden
ratio. For every natural number $k$,
$F_{2k+1} \varphi = F_{2k+2} + \left((\sqrt 5 - 1)/2\right)^{2k+1}$ and
$F_{2k+1} (1 + \varphi) = F_{2k+3} + \left((\sqrt 5 - 1)/2\right)^{2k+1}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 1. -/
public theorem fib_odd_mul_goldenRatio (k : ℕ) :
    (Nat.fib (2 * k + 1) : ℝ) * Real.goldenRatio =
        Nat.fib (2 * k + 2) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) ∧
      (Nat.fib (2 * k + 1) : ℝ) * (1 + Real.goldenRatio) =
        Nat.fib (2 * k + 3) + ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) := by
  have hpow : ((Real.sqrt 5 - 1) / 2) ^ (2 * k + 1) = -Real.goldenConj ^ (2 * k + 1) := by
    rw [← (odd_two_mul_add_one k).neg_pow]
    congr 1
    ring
  have hbinet := Real.fib_succ_sub_goldenRatio_mul_fib (2 * k + 1)
  have hfib : (Nat.fib (2 * k + 3) : ℝ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
    exact_mod_cast Nat.fib_add_two (n := 2 * k + 1)
  rw [hpow, hfib]
  constructor <;> linarith

end MetaMathlibExt
