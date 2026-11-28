/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.LinearCombination

/-!
# Odd solutions of equation (7) for two-near perfect numbers
-/

namespace MetaMathlibExt

/-- **No odd solutions of $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p + 1$ for
$2 \le b \le k - 1$.** Let $b$ and $k$ be natural numbers with $2 \le b$ and $b + 1 \le k$, and
let $p$ be an odd natural number. Then $(2^{k+1} - 1)(p^2 + p + 1) \ne 2^{k+1} p^2 + 2^b p + 1$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 4
(`integers-2024-A61-lem-4`). -/
public theorem not_two_near_perfect_eq_seven {b k p : ℕ} (hp : Odd p) (hb : 2 ≤ b)
    (hbk : b + 1 ≤ k) :
    ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) ≠ 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1 := by
  intro heq
  have hpow : (2 : ℤ) ^ b ≤ 2 ^ k := pow_le_pow_right₀ (by decide) (by omega)
  have hpos : 0 < (2 : ℤ) ^ b - 2 := by
    have : (4 : ℤ) ≤ 2 ^ b := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hb
    omega
  -- Factoring gives both a divisor of 2 ^ b - 2 and its quotient.
  have hfactor : ((p : ℤ) + 1) * (p - (2 * 2 ^ k - 2 ^ b)) = 2 ^ b - 2 := by
    rw [pow_succ'] at heq
    linear_combination -heq
  have hle : (p : ℤ) + 1 ≤ 2 ^ b - 2 := Int.le_of_dvd hpos ⟨_, hfactor.symm⟩
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rw [← hfactor, mul_pos_iff_of_pos_left (add_pos hp' zero_lt_one)] at hpos
  omega

end MetaMathlibExt
