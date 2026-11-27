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
# Prefix sums of Lucas-Leonardo `p`-numbers

The defining recurrence writes each summand as a difference of consecutive shifted terms
minus `p`. Induction telescopes these differences without using the bracelet interpretation.

## References

* Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo p-Numbers and
  Lucas-Leonardo p-Numbers*, INTEGERS 25 (2025), Article A57, pp. 1–17, Section 3,
  Proposition 15 (p. 13).
* J. Zhong, J. Yao, and C.-L. Chung, *A Note on Incomplete Fibonacci–Lucas Relations*,
  Symmetry 15 (2023), no. 12, Article 2113, Section 3, defines the Lucas-Leonardo `p`-numbers
  by the recurrence credited in Belkhir and Tan's equation (5).
-/

namespace MetaMathlibExt

/-- **Sum of the Lucas-Leonardo p-numbers.** For every natural number $p \ge 1$ and every natural
number $n$, the Lucas-Leonardo $p$-numbers $R_{p,m}$ satisfy
$\sum_{i=0}^{n} R_{p,i} = R_{p,n+p+1} - p(n + 1) - 1$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 15. -/
public theorem sum_lucasLeonardoP (p n : ℕ) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range (n + 1), lucasLeonardoP p i =
      lucasLeonardoP p (n + p + 1) - p * ((n : ℤ) + 1) - 1 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, Nat.zero_add, lucasLeonardoP_of_lt p (Nat.lt_succ_self p),
      show p.succ - 1 = p by omega, show p.succ - p - 1 = 0 by omega,
      lucasLeonardoP_of_le p hp le_rfl]
    push_cast
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      lucasLeonardoP_of_lt p (show p < n + 1 + p + 1 by omega),
      show n + 1 + p + 1 - 1 = n + p + 1 by omega,
      show n + 1 + p + 1 - p - 1 = n + 1 by omega]
    push_cast
    ring

end MetaMathlibExt
