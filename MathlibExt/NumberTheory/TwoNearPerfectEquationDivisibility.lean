/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.LinearCombination

/-!
# Divisibility by `p + 1` for odd solutions of equation (12) for two-near perfect numbers
-/

namespace MetaMathlibExt

-- The equation alone gives the quotient. Primality is not needed, even though the paper
-- applies the result to odd primes.
set_option linter.unusedVariables false in
/-- **Odd solutions $p$ of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$ satisfy
$p + 1 \mid 2^b + 2$.** Let $k$ and $b$ be positive natural numbers and let $p$ be an odd natural
number such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$. Then, as integers,
$p + 1$ divides $2^b + 2$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 7
(`integers-2024-A61-lem-7`). -/
public theorem succ_dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k)
    (hb : 0 < b) (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p + 1 : ℤ) ∣ 2 ^ b + 2 := by
  refine ⟨(2 : ℤ) ^ (k + 1) + 2 ^ b - (2 ^ b + 1) * p, ?_⟩
  linear_combination -h

end MetaMathlibExt
