/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic
public import MathlibExt.NumberTheory.SophieGermainPrime
import Mathlib.Data.Nat.Prime.Basic

/-!
# Primes that are not Sophie Germain primes

The factorization `2 * q + 1 = p * (2 * r + 1)` relates each arithmetic progression
to the odd multiples of its indexing prime `p`.
-/

public section

namespace MetaMathlibExt

/-- **Primes that are not Sophie Germain primes.** For an odd prime $p$, let
$A(p) = \{pr + (p - 1)/2 : r = 1, 2, 3, \dots\}$, and let $A$ be the union of the sets $A(p)$ over
all odd primes $p$. A prime is not a Sophie Germain prime if and only if it lies in $A$;
equivalently, the Sophie Germain primes are exactly the primes outside $A$.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 2.1 (`integers-2025-A83-thm-2-1`). -/
theorem setOf_prime_not_isSophieGermainPrime_eq_inter :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime} =
      {q : ℕ | q.Prime} ∩
        {q : ℕ | ∃ p r : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ r ∧ q = p * r + (p - 1) / 2} := by
  ext q
  have factor {p r : ℕ} (hp : Odd p) :
      2 * q + 1 = p * (2 * r + 1) ↔ q = p * r + (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := hp
    rw [mul_add, mul_one, mul_left_comm p 2 r]
    omega
  constructor
  · rintro ⟨hq, h⟩
    obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd (n := 2 * q + 1) (by
      have := hq.two_le
      omega)
    have hodd : Odd (p * k) := ⟨q, hk.symm⟩
    obtain ⟨hpOdd, r, rfl⟩ := Nat.odd_mul.mp hodd
    refine ⟨hq, p, r, hp, ?_, ?_, (factor hpOdd).mp hk⟩
    · rintro rfl
      exact (by decide : ¬ Odd (2 : ℕ)) hpOdd
    · apply Nat.pos_of_ne_zero
      rintro rfl
      have heq : 2 * q + 1 = p := by simpa using hk
      exact h ⟨hq, heq ▸ hp⟩
  · rintro ⟨hq, p, r, hp, hp₂, hr, heq⟩
    refine ⟨hq, fun h => ?_⟩
    have hprod := (factor (hp.odd_of_ne_two hp₂)).mpr heq
    exact Nat.not_prime_of_mul_eq hprod.symm hp.ne_one (by omega) h.prime_two_mul_add_one

end MetaMathlibExt
