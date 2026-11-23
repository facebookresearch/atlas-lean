/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Divisibility for odd solutions of equation (6) for two-near perfect numbers
-/

namespace MetaMathlibExt

/-- **Divisibility constraints on odd solutions of $(2^{k+1} - 1)(p^2 + p + 1) =
2^{k+1} p^2 + 2^b p + 1$.** Let $b$ and $k$ be natural numbers and let $p$ be an odd natural
number such that $(2^{k+1} - 1)(p^2 + p + 1) = 2^{k+1} p^2 + 2^b p + 1$. Then, as integers, $p$
divides $2^k - 1$ and $p + 1$ divides $2^b - 2$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 3
(`integers-2024-A61-lem-3`). -/
public theorem dvd_of_two_near_perfect_eq_six {b k p : ℕ} (hp : Odd p)
    (h : ((2 : ℤ) ^ (k + 1) - 1) * (p ^ 2 + p + 1) = 2 ^ (k + 1) * p ^ 2 + 2 ^ b * p + 1) :
    (p : ℤ) ∣ 2 ^ k - 1 ∧ (p + 1 : ℤ) ∣ 2 ^ b - 2 := by
  rw [pow_succ'] at h
  constructor
  · apply (hp.natCast (R := ℤ)).isCoprime_two.dvd_of_dvd_mul_left
    refine ⟨(p : ℤ) + 1 + 2 ^ b - 2 * 2 ^ k, ?_⟩
    linear_combination h
  · refine ⟨(p : ℤ) + 2 ^ b - 2 * 2 ^ k, ?_⟩
    linear_combination h

end MetaMathlibExt
