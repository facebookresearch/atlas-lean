/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Bounds.Defs
import Mathlib.Data.ZMod.Basic

/-! # Periodic tails of generalized Fermat numbers modulo a prime square -/

namespace MetaMathlibExt

/-- A constant tail starts the period if every earlier tail contains a different value. -/
private theorem isLeast_periodic_start_of_constant_tail {α : Type*} {f : ℕ → α} {s : ℕ} {v : α}
    (hconst : ∀ n, s ≤ n → f n = v) (hearlier : ∀ m < s, ∃ j, m ≤ j ∧ f j ≠ v) :
    IsLeast {m : ℕ | ∃ T, 0 < T ∧ Function.Periodic (fun k => f (m + k)) T} s := by
  refine ⟨⟨1, by decide, fun k => (hconst _ (by omega)).trans (hconst _ (by omega)).symm⟩, ?_⟩
  rintro m ⟨T, hT, hperiod⟩
  by_contra! hm
  obtain ⟨j, hmj, hj⟩ := hearlier m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmj
  -- Repeating the period moves the exceptional value into the constant tail.
  apply hj
  have hs := Nat.le_mul_of_pos_right s hT
  have hrepeat : f (m + (k + s * T)) = f (m + k) := hperiod.nat_mul s k
  exact hrepeat.symm.trans (hconst _ (by omega))

set_option linter.unusedVariables false in
/-- **Start of the period of generalized Fermat numbers modulo the square of a prime.** For
natural numbers $a$, $b$ and $k$ write $F_k(a, b) = a^{b^k} + 1$. Let $a, b \ge 2$, let $p$ be a
prime, and let $n_0$ be the least natural number with $p^2 \mid F_{n_0}(a, b)$. Say that the
sequence $(F_k(a, b))_k$ is periodic modulo $p^2$ from index $m$ if there is a $T > 0$ with
$F_{m+k+T}(a, b) \equiv F_{m+k}(a, b) \pmod{p^2}$ for every $k \ge 0$. If $b$ is odd, then $n_0$
is the least index from which the sequence is periodic modulo $p^2$; if $b$ is even, this least
index is $n_0 + 1$.

In the source's terms, $n_0$ is the index of the first term of the period when $b$ is odd, and
the index of the last term of the pre-period when $b$ is even.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 2 (`integers-2026-A77-cor-2`). -/
public theorem isLeast_periodic_start_pow_pow_add_one_mod_sq {a b p n₀ : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) (hp : p.Prime) (hn₀ : p ^ 2 ∣ a ^ b ^ n₀ + 1)
    (hmin : ∀ n < n₀, ¬ p ^ 2 ∣ a ^ b ^ n + 1) :
    (Odd b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} n₀) ∧
      (Even b → IsLeast {m : ℕ | ∃ T, 0 < T ∧
        Function.Periodic (fun k => (a ^ b ^ (m + k) + 1) % p ^ 2) T} (n₀ + 1)) := by
  let F (n : ℕ) := (a ^ b ^ n + 1) % p ^ 2
  have hneg : (a : ZMod (p ^ 2)) ^ b ^ n₀ = -1 := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).2 hn₀
  have hshift (k : ℕ) : F (n₀ + k) = ((-1 : ZMod (p ^ 2)) ^ b ^ k + 1).val := by
    dsimp only [F]
    rw [← ZMod.val_natCast, Nat.cast_add, Nat.cast_pow, Nat.cast_one, pow_add, pow_mul, hneg]
  constructor
  · intro hbodd
    apply isLeast_periodic_start_of_constant_tail (f := F) (v := 0)
    · intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [hshift, (hbodd.pow (n := k)).neg_one_pow, neg_add_cancel, ZMod.val_zero]
    · exact fun m hm => ⟨m, le_rfl, fun h => hmin m hm (Nat.dvd_of_mod_eq_zero h)⟩
  · intro hbeven
    apply isLeast_periodic_start_of_constant_tail (f := F) (v := 2)
    · intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have he : Even (b ^ (1 + k)) := hbeven.pow_of_ne_zero (by omega)
      have hp₂ : 2 < p ^ 2 := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_left hp.two_le 2)
      rw [Nat.add_assoc, hshift, he.neg_one_pow, one_add_one_eq_two, ZMod.val_ofNat_of_lt hp₂]
    · intro m hm
      refine ⟨n₀, by omega, ?_⟩
      simp [F, Nat.mod_eq_zero_of_dvd hn₀]

end MetaMathlibExt
