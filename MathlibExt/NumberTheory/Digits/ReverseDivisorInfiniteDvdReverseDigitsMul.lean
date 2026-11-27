/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.Digits.ReverseDivisibility
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Infinitely many multiples with divisible reversal

If a natural number `n` is not divisible by `10` and divides the decimal reversal of one of
its positive multiples, then `n` divides the decimal reversal of infinitely many of its
positive multiples (`infinite_dvd_reverseDigits_mul`). Given such a multiple `m`, repeating
its decimal block with zero padding gives multiples `m * (10 ^ t + 1)` whose reversals are
the reversal of `m` times `10 ^ t + 1`.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
*INTEGERS* 25 (2025), Article A37 (<https://math.colgate.edu/~integers/vol25.html>),
Proposition 6.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- Repeating a decimal block with zero padding multiplies its reversal: for `0 < m`, the
decimal reversal of `m + 10 ^ (L + k) * m`, where `L` is the number of decimal digits of `m`,
equals the reversal of `m` times `10 ^ (L + k) + 1`. -/
private theorem reverseDigits_add_pow_mul_self (m k : ℕ) (hm : 0 < m) :
    Nat.reverseDigits 10 (m + 10 ^ ((Nat.digits 10 m).length + k) * m)
      = Nat.reverseDigits 10 m * (10 ^ ((Nat.digits 10 m).length + k) + 1) := by
  have hdig := Nat.digits_append_zeroes_append_digits (b := 10) (n := m) (m := m) (k := k)
    (by decide) hm
  simp only [Nat.reverseDigits]
  rw [← hdig]
  have hrev : (Nat.digits 10 m ++ List.replicate k 0 ++ Nat.digits 10 m).reverse
      = (Nat.digits 10 m).reverse ++
        (List.replicate k 0 ++ (Nat.digits 10 m).reverse) := by
    simp [List.reverse_append]
  rw [hrev, Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
    List.length_reverse, List.length_replicate, zero_add, ← mul_assoc, ← pow_add]
  ring

/-- **Infinitely many multiples with divisible reversal.** Let $n$ be a natural number not
divisible by $10$, and suppose that $n$ divides the decimal reversal of $k_0 n$ for some natural
number $k_0 \ge 1$. Then there are infinitely many natural numbers $k \ge 1$ such that $n$
divides the decimal reversal of $k n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
public theorem infinite_dvd_reverseDigits_mul (n : ℕ)
    (h10 : ¬ 10 ∣ n)
    (h : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n)) :
    Set.Infinite
      {k : ℕ | 1 ≤ k ∧ n ∣ Nat.reverseDigits 10 (k * n)} := by
  obtain ⟨k₀, hk₀, hdvd⟩ := h
  have hn : 0 < n := by
    rcases eq_zero_or_pos n with rfl | hpos
    · simp at h10
    · exact hpos
  have hm : 0 < k₀ * n := Nat.mul_pos (by omega) hn
  have hmem : ∀ s : ℕ, k₀ * (10 ^ ((Nat.digits 10 (k₀ * n)).length + s) + 1) ∈
      {k : ℕ | 1 ≤ k ∧ n ∣ Nat.reverseDigits 10 (k * n)} := by
    intro s
    refine ⟨?_, ?_⟩
    · calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
        _ ≤ k₀ * (10 ^ ((Nat.digits 10 (k₀ * n)).length + s) + 1) :=
          Nat.mul_le_mul hk₀ (Nat.le_add_left 1 _)
    · have hmul : k₀ * (10 ^ ((Nat.digits 10 (k₀ * n)).length + s) + 1) * n
          = k₀ * n + 10 ^ ((Nat.digits 10 (k₀ * n)).length + s) * (k₀ * n) := by
        ring
      rw [hmul, reverseDigits_add_pow_mul_self _ _ hm]
      exact dvd_mul_of_dvd_left hdvd _
  have hinj : Function.Injective
      (fun s : ℕ => k₀ * (10 ^ ((Nat.digits 10 (k₀ * n)).length + s) + 1)) := by
    intro a b hab
    dsimp only at hab
    have h1 : 10 ^ ((Nat.digits 10 (k₀ * n)).length + a) + 1
        = 10 ^ ((Nat.digits 10 (k₀ * n)).length + b) + 1 :=
      mul_left_cancel₀ (by omega) hab
    have h2 : 10 ^ ((Nat.digits 10 (k₀ * n)).length + a)
        = 10 ^ ((Nat.digits 10 (k₀ * n)).length + b) := Nat.add_right_cancel h1
    have h3 : (Nat.digits 10 (k₀ * n)).length + a
        = (Nat.digits 10 (k₀ * n)).length + b :=
      Nat.pow_right_injective (a := 10) (by decide) h2
    omega
  exact Set.infinite_of_injective_forall_mem hinj hmem

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
