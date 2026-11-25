/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.PowAddPowEqSq

/-!
# Prime powers one less than a square

Writing the square root as `k + 1` gives the factorization `k * (k + 2) = p ^ x`.
Both factors are powers of the same prime, so the smaller divides the larger and hence
divides their difference, two.
-/

namespace MetaMathlibExt

/-- **Prime powers one less than a square.** Let $p$ be a prime. Then non-negative integers $x$
and $y$ satisfy $p^x + 1 = y^2$ if and only if $(p, x, y) = (2, 3, 3)$ or $(p, x, y) = (3, 1, 2)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 2. -/
public theorem prime_pow_add_one_eq_sq_iff {p : ℕ} (hp : p.Prime) (x y : ℕ) :
    p ^ x + 1 = y ^ 2 ↔ (p, x, y) = (2, 3, 3) ∨ (p, x, y) = (3, 1, 2) := by
  constructor
  · intro h
    obtain _ | k := y
    · simp at h
    have hfac : k * (k + 2) = p ^ x := by nlinarith only [h]
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hfac)
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hfac)
    have hab : a ≤ b := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by omega)
    have hk : k ∣ k + 2 := by
      rw [hb, ha]
      exact pow_dvd_pow p hab
    have hk2 := (Nat.dvd_add_right (dvd_refl k)).mp hk
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp (show p ^ x = 3 from hfac.symm)
      exact Or.inr rfl
    · have hd : 2 ∣ p ^ x := Dvd.intro _ hfac
      obtain rfl := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hp hd
      obtain ⟨rfl, _⟩ := (two_pow_add_one_eq_sq x 3).mp h
      exact Or.inl rfl
  · simp only [Prod.mk.injEq]
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> rfl

end MetaMathlibExt
