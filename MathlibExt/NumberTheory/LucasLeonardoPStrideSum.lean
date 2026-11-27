/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.LeonardoPTilings
import Mathlib.Tactic.Ring

/-!
# Sums of Lucas–Leonardo `p`-numbers at multiples of `p + 1`

Each step of the sum is one instance of the recurrence
`R_{p,m} = R_{p,m-1} + R_{p,m-p-1} + p` at `m = (p + 1)(n + 1) + 1`, so the sum telescopes.
-/

namespace MetaMathlibExt

/-- **Sum of the Lucas-Leonardo p-numbers at multiples of $p + 1$.** For every natural number
$p \ge 1$ and every natural number $n$, the Lucas-Leonardo $p$-numbers $R_{p,m}$ satisfy
$\sum_{i=0}^{n} R_{p,(p+1)i} = R_{p,(p+1)n+1} - p(n - p - 1)$, an identity of integers.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 16. -/
public theorem sum_lucasLeonardoP_stride (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p ((p + 1) * i) =
      lucasLeonardoP p ((p + 1) * n + 1) - p * ((n : ℤ) - p - 1) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, Nat.mul_zero, Nat.zero_add, lucasLeonardoP_zero,
      lucasLeonardoP_of_le p le_rfl hp]
    push_cast
    ring
  | succ n ih =>
    have hstep : (p + 1) * (n + 1) = (p + 1) * n + p + 1 := by rw [Nat.mul_succ]; omega
    rw [Finset.sum_range_succ, ih,
      lucasLeonardoP_of_lt p (show p < (p + 1) * (n + 1) + 1 by omega),
      Nat.add_sub_cancel, show (p + 1) * (n + 1) + 1 - p - 1 = (p + 1) * n + 1 by omega]
    push_cast
    ring

end MetaMathlibExt
