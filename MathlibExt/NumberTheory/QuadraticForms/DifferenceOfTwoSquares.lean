/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/--
**Positive integers that are differences of two squares.** A positive natural number $n$ can be
written as $n = a^2 - b^2$ with natural numbers $a$ and $b$ if and only if there is no natural
number $k$ with $n = 4k + 2$.

Proves `Wanted` entry `nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two`.

Source: Arias, Borja, and Rubio cite D. M. Burton, "Elementary Number Theory," 7th edition,
Theorem 13.4; truncated subtraction is exact on the witnesses.

Source: Fabián Arias, Jerson Borja, and Luis Rubio, "Counting
Integers Representable as Images of Polynomials Modulo n," Journal
of Integer Sequences 22 (2019), Article 19.6.7, Theorem (label
teoburton), lines 821–823,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Borja/borja3.tex
-/
theorem nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two
    (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℕ, n = a ^ 2 - b ^ 2) ↔ ¬ ∃ k : ℕ, n = 4 * k + 2 := by
  constructor
  · rintro ⟨a, b, hab⟩ ⟨k, hk⟩
    by_cases hle : b ≤ a
    · have h2 : n + b ^ 2 = a ^ 2 := by omega
      have ha4 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
        have hr : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        have hp : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := Nat.pow_mod a 2 4
        rcases hr with r | r | r | r <;> rw [hp, r] <;> decide
      have hb4 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
        have hr : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        have hp : b ^ 2 % 4 = (b % 4) ^ 2 % 4 := Nat.pow_mod b 2 4
        rcases hr with r | r | r | r <;> rw [hp, r] <;> decide
      omega
    · have hlt : a < b := lt_of_not_ge hle
      have hzero : a ^ 2 - b ^ 2 = 0 :=
        Nat.sub_eq_zero_of_le (Nat.pow_le_pow_left (le_of_lt hlt) 2)
      omega
  · intro hne
    have hmod2 : n % 4 ≠ 2 := by
      intro hcon
      apply hne
      exact ⟨n / 4, by have h1 := Nat.div_add_mod n 4; omega⟩
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by omega
    clear hne hmod2
    rcases hmod with h0 | h1 | h3
    · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k := ⟨n / 4, by have hd := Nat.div_add_mod n 4; omega⟩
      have hkpos : 0 < k := by omega
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
      refine ⟨t + 2, t, ?_⟩
      have hle : t ^ 2 ≤ (t + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (t + 2) ^ 2 = 4 * (t + 1) + t ^ 2 := by ring
      omega
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 :=
        ⟨2 * (n / 4), by have hd := Nat.div_add_mod n 4; omega⟩
      refine ⟨m + 1, m, ?_⟩
      have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (m + 1) ^ 2 = (2 * m + 1) + m ^ 2 := by ring
      omega
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 :=
        ⟨2 * (n / 4) + 1, by have hd := Nat.div_add_mod n 4; omega⟩
      refine ⟨m + 1, m, ?_⟩
      have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (m + 1) ^ 2 = (2 * m + 1) + m ^ 2 := by ring
      omega

end MetaMathlibExt
