/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.ZMod.Basic
import MathlibExt.NumberTheory.Diophantine.PowerSquare

/-!
# Squares of the form `p ^ x + (2 * p - 1) ^ y` for prime pairs

Reduction modulo three forces the prime pair to be `(3, 5)`. Modulo twenty, the powers of three
cycle through `1, 3, 9, 7` and every positive power of five is five. Adding five to any of the
four residues cannot give a square, so the equation reduces to `3 ^ x + 1 = z ^ 2`.
-/

namespace MetaMathlibExt

namespace prime_pair_pow_add_pow_eq_sq_iff

private theorem prime_eq_three {p x y z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (h : p ^ x + (2 * p - 1) ^ y = z ^ 2) : p = 3 := by
  by_contra hp3
  have hp_min := hp.two_le
  have hp_ndvd : ¬3 ∣ p := fun hd => hp3 ((Nat.dvd_prime_two_le hp (by decide)).mp hd).symm
  have hq_ndvd : ¬3 ∣ 2 * p - 1 := by
    intro hd
    have := (Nat.dvd_prime_two_le hq (by decide)).mp hd
    omega
  have hp_mod : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).mpr (by omega)
  have hq_mod : ((2 * p - 1 : ℕ) : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' _ 1 3).mpr (by omega)
  have heq := congrArg (Nat.cast : ℕ → ZMod 3) h
  simp only [Nat.cast_add, Nat.cast_pow, hp_mod, hq_mod, one_pow] at heq
  exact (by decide : ∀ a : ZMod 3, 1 + 1 ≠ a ^ 2) z heq

private theorem five_exponent_eq_zero {x y z : ℕ} (h : 3 ^ x + 5 ^ y = z ^ 2) : y = 0 := by
  by_contra hy
  have heq : (3 : ZMod 20) ^ x + 5 ^ y = (z : ZMod 20) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (Nat.cast : ℕ → ZMod 20) h
  have h₃ : (3 : ZMod 20) ^ 4 = 1 := by decide
  have h₅ : IsIdempotentElem (5 : ZMod 20) := rfl
  rw [pow_eq_pow_mod x h₃, h₅.pow_eq hy] at heq
  have residues : ∀ (i : Fin 4) (a : ZMod 20), (3 : ZMod 20) ^ i.val + 5 ≠ a ^ 2 := by decide
  exact residues ⟨x % 4, Nat.mod_lt _ (by decide)⟩ z heq

end prime_pair_pow_add_pow_eq_sq_iff

open prime_pair_pow_add_pow_eq_sq_iff

/-- **Squares of the form $p^x + (2p - 1)^y$ for prime pairs.** Let $p$ be an odd prime such that
$2p - 1$ is prime. Then non-negative integers $x$, $y$ and $z$ satisfy $p^x + (2p - 1)^y = z^2$
if and only if $p = 3$ and $(x, y, z) = (1, 0, 2)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 1. -/
public theorem prime_pair_pow_add_pow_eq_sq_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (x y z : ℕ) :
    p ^ x + (2 * p - 1) ^ y = z ^ 2 ↔ (p, x, y, z) = (3, 1, 0, 2) := by
  constructor
  · intro h
    obtain rfl := prime_eq_three hp hp2 hq h
    change 3 ^ x + 5 ^ y = z ^ 2 at h
    obtain rfl := five_exponent_eq_zero h
    cases x with
    | zero =>
      exact False.elim ((Nat.prime_iff.mp Nat.prime_two).not_isSquare ⟨z, by simpa [sq] using h⟩)
    | succ x =>
      obtain rfl := Nat.eq_zero_of_three_pow_succ_add_one_eq_sq h
      have hz : z = 2 := Nat.pow_left_injective two_ne_zero (show z ^ 2 = 2 ^ 2 from h.symm)
      simp [hz]
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    decide

end MetaMathlibExt
