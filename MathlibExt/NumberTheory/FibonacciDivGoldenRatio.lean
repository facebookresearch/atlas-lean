/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci numbers divided by the golden ratio

Let $F_n$ be the $n$-th Fibonacci number and $\varphi = (1 + \sqrt{5})/2$ the golden ratio. This
file proves Wesley's identity `fib_div_goldenRatio_sub_fib`: for every $n \ge 2$,
$F_n/\varphi - F_{n-1} = (-1)^{n+1}\varphi^{-n}$. Since $0 < \varphi^{-n} < 1/2$ for $n \ge 2$,
the identity says that $F_{n-1}$ is the integer nearest to $F_n/\varphi$, below it for odd $n$
and above it for even $n$.

## Implementation notes

Write $\psi = (1 - \sqrt{5})/2$ for the conjugate of $\varphi$. Then $\varphi^{-1} = -\psi$
(`Real.inv_goldenRatio`) and $\psi F_n + F_{n-1} = \psi^n$ for $n \ge 1$
(`Real.goldenConj_mul_fib_succ_add_fib`), so the left-hand side is $-\psi^n$, while
$(-1)^{n+1}\varphi^{-n} = (-1)^{n+1}(-\psi)^n = -\psi^n$. The identity therefore holds for every
$n \ge 1$; the hypothesis $n \ge 2$ is the source's. The Lean statement fails for $n = 0$, where
`Nat.fib (0 - 1)` is `Nat.fib 0 = 0` because subtraction of natural numbers truncates.

## References

* William J. Wesley, *Improved Ramsey-type theorems for Fibonacci numbers and other sequences*,
  INTEGERS 25 (2025), Article A29; preprint arXiv:2211.05167, Corollary 4.
-/

namespace MetaMathlibExt

/-- **Fibonacci numbers divided by the golden ratio.** Let $F_n$ be the $n$-th Fibonacci number,
with $F_0 = 0$ and $F_1 = 1$, and let $\varphi = (1 + \sqrt{5})/2$ be the golden ratio. For every
natural number $n \ge 2$,
$$\frac{F_n}{\varphi} - F_{n-1} = (-1)^{n+1} \varphi^{-n}.$$

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Corollary 1 (`integers-2025-A29-cor-1`). -/
public theorem fib_div_goldenRatio_sub_fib (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℝ) / Real.goldenRatio - Nat.fib (n - 1) =
      (-1) ^ (n + 1) * Real.goldenRatio ^ (-(n : ℤ)) := by
  -- `ψ F_n + F_{n-1} = ψ ^ n`, and `φ⁻¹ = -ψ` turns `φ ^ (-n)` into `(-ψ) ^ n`.
  have h := Real.goldenConj_mul_fib_succ_add_fib (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  rw [div_eq_mul_inv, zpow_neg, zpow_natCast, ← inv_pow, Real.inv_goldenRatio, pow_succ',
    mul_assoc, ← mul_pow]
  linear_combination -h

end MetaMathlibExt
