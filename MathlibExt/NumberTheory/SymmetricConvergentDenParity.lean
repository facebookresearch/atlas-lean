/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence

/-! # Parity of symmetric continued fractions with odd period length

Splitting the final denominator at the midpoint gives a sum of two squares.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Parity of $q_{l-1}$ for a symmetric sequence, odd $l$.** Let $l \ge 3$ be odd and let
$a_0, a_1, a_2, \dots$ be natural numbers with convergent denominators $q_0, q_1, q_2, \dots$,
such that $a_i = a_{l-i}$ for $1 \le i < l$. Then
$q_{l-1} \equiv q_{(l-1)/2} + q_{(l-3)/2} \pmod 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 2 (i)
(`integers-2026-A69-cor-2`). -/
theorem convergentDen_parity_of_odd (l : ℕ) (hl : Odd l) (hl3 : 3 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡
      convergentDen a ((l - 1) / 2) + convergentDen a ((l - 3) / 2) [MOD 2] := by
  obtain ⟨m, hm⟩ := hl
  rw [convergentDen_symm_split l a hsymm m (by omega) (by omega),
    show l - 1 - m = m by omega, show l - 2 - m = m - 1 by omega,
    show (l - 1) / 2 = m by omega, show (l - 3) / 2 = m - 1 by omega]
  have hsq (n : ℕ) : n * n ≡ n [MOD 2] := by
    rw [Nat.ModEq, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  exact (hsq _).add (hsq _)

end

end MetaMathlibExt
