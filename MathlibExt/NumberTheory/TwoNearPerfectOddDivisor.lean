/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The odd-divisor condition for 2-near-perfect equation (12)

Rearranging the equation gives divisibility by the odd modulus after multiplication by two.
Writing the modulus as `2 * r + 1` cancels that factor without a primality assumption.
-/

namespace MetaMathlibExt

-- The paper assumes positive exponents, though cancellation does not need their positivity.
set_option linter.unusedVariables false in
/-- **Odd solutions $p$ of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$ divide
$2^k - 1$.** Let $k$ and $b$ be positive natural numbers and let $p$ be an odd natural number
such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p^2 + 1$. Then $p$ divides $2^k - 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 6
(`integers-2024-A61-lem-6`). -/
public theorem dvd_of_two_near_perfect_eq_twelve {b k p : ℕ} (hk : 0 < k) (hb : 0 < b)
    (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p ^ 2 + 1) :
    (p : ℤ) ∣ 2 ^ k - 1 := by
  have h₂ : (p : ℤ) ∣ 2 * ((2 : ℤ) ^ k - 1) := by
    refine ⟨(1 + 2 ^ b) * p - (2 ^ (k + 1) - 1), ?_⟩
    rw [pow_succ (2 : ℤ) k] at h ⊢
    linear_combination h
  obtain ⟨r, hr⟩ := hp
  have hpz : (p : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hr
  have he : (p : ℤ) * ((2 : ℤ) ^ k - 1) - (r : ℤ) * (2 * (2 ^ k - 1)) = 2 ^ k - 1 := by
    rw [hpz]
    ring
  rw [← he]
  exact dvd_sub (dvd_mul_right _ _) (h₂.mul_left _)

end MetaMathlibExt
