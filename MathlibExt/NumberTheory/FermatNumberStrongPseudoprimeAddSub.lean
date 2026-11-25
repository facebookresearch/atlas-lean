/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Fermat
public import MathlibExt.NumberTheory.StrongPseudoprime
import Mathlib.Tactic.LinearCombination

/-!
# Strong pseudoprime bases of the form `2 ^ (2 ^ (k - 1) + t) ± 2 ^ t`

Both bases raised to `2 ^ (k + 1)` are `-1` modulo the composite Fermat number
`Nat.fermatNumber k`, so both pass its strong pseudoprime test.
-/

namespace MetaMathlibExt

/-- **Strong pseudoprime bases $2^{2^{k-1}+t} \pm 2^t$ of composite Fermat numbers.** Let $k$ be a
natural number such that the Fermat number $F_k = 2^{2^k} + 1$ is composite. Then for every
natural number $t$, $F_k$ is a strong pseudoprime to both bases $2^{2^{k-1}+t} + 2^t$ and
$2^{2^{k-1}+t} - 2^t$, computed modulo $F_k$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 7 (`integers-2024-A23-thm-7`). -/
public theorem fermatNumber_isStrongPseudoprime_two_pow_add_sub {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) (t : ℕ) :
    IsStrongPseudoprime (Nat.fermatNumber k) (2 ^ (2 ^ (k - 1) + t) + 2 ^ t) ∧
      IsStrongPseudoprime (Nat.fermatNumber k) (2 ^ (2 ^ (k - 1) + t) - 2 ^ t) := by
  -- The first two Fermat numbers are prime, so we may write `k = m + 2`.
  have hk₂ : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> exact hk (by decide)
  obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hF : (2 : ZMod (Nat.fermatNumber k)) ^ 2 ^ k = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast ZMod.natCast_self (Nat.fermatNumber k)
  let x := (2 : ZMod (Nat.fermatNumber k)) ^ 2 ^ (k - 1)
  have hx : x ^ 2 = -1 := by
    dsimp only [x]
    rwa [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have strong (b : ZMod (Nat.fermatNumber k)) (hb : b ^ 4 = -4) :
      IsStrongPseudoprime (Nat.fermatNumber k) (b * 2 ^ t) := by
    have hi : k + 1 < 2 ^ k := by
      rw [hm, pow_add]
      have := m.lt_two_pow_self
      omega
    refine ⟨lt_trans Nat.one_lt_two (Nat.two_lt_fermatNumber k), hk, Nat.odd_fermatNumber k,
      2 ^ k, 1, by simp [Nat.fermatNumber], odd_one, Or.inr ⟨k + 1, hi, ?_⟩⟩
    -- The factor `2 ^ t` disappears at the witness exponent.
    have ht : ((2 : ZMod (Nat.fermatNumber k)) ^ t) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_right_comm, pow_succ, pow_mul, hF, neg_one_sq, one_pow]
    rw [mul_one, mul_pow, ht, mul_one]
    -- Since `b ^ 8 = 16`, raising both sides to `2 ^ m` gives the Fermat congruence.
    have hb₈ : b ^ (2 ^ 3 : ℕ) = (2 : ZMod (Nat.fermatNumber k)) ^ (2 ^ 2 : ℕ) := by
      change b ^ (4 * 2) = 2 ^ 4
      rw [pow_mul, hb]
      ring
    rw [show k + 1 = 3 + m by omega, pow_add, pow_mul, hb₈, ← pow_mul, ← pow_add,
      show 2 + m = k by omega, hF]
  rw [pow_add, ← add_one_mul, ← sub_one_mul]
  change IsStrongPseudoprime _ ((x + 1) * 2 ^ t) ∧ IsStrongPseudoprime _ ((x - 1) * 2 ^ t)
  constructor
  · apply strong
    linear_combination (x ^ 2 + 4 * x + 5) * hx
  · apply strong
    linear_combination (x ^ 2 - 4 * x + 5) * hx

end MetaMathlibExt
