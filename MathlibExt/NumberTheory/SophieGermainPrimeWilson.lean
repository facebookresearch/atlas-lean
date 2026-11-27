/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.NumberTheory.SophieGermainPrime
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.LinearCombination

/-!
# Wilson's criterion for Sophie Germain primes

Splitting the modulus into its coprime factors gives Wilson's congruence modulo
`a` and the two possible signs of `a!` modulo `2 * a + 1`.
-/

namespace MetaMathlibExt

namespace isSophieGermainPrime_ne_two_iff_factorial_modEq

private theorem split_residues {a : ℕ} (ha : 2 ≤ a) :
    (((a - 1).factorial : ℤ) ≡ 2 * a - 1 [ZMOD a * (2 * a + 1)] ∨
      ((a - 1).factorial : ℤ) ≡ -(6 * a + 1) [ZMOD a * (2 * a + 1)]) ↔
      a.Prime ∧ ((a.factorial : ZMod (2 * a + 1)) = 1 ∨
        (a.factorial : ZMod (2 * a + 1)) = -1) := by
  let q := 2 * a + 1
  have hq : (q : ℤ) = 2 * a + 1 := by simp [q]
  have hcop : (a : ℤ).natAbs.Coprime (q : ℤ).natAbs := by
    change a.Coprime (2 * a + 1)
    simp [Nat.coprime_mul_right_add_right]
  have hzero : 2 * (a : ZMod q) + 1 = 0 := by
    simpa only [q, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
      using ZMod.natCast_self q
  -- In this ring, multiplication by `a` has inverse multiplication by `-2`.
  have hfac (r : ZMod q) :
      ((a - 1).factorial : ZMod q) = -2 * r ↔ (a.factorial : ZMod q) = r := by
    rw [← Nat.mul_factorial_pred (show a ≠ 0 by omega), Nat.cast_mul]
    constructor
    · intro h
      rw [h]
      linear_combination -r * hzero
    · rintro rfl
      linear_combination ((a - 1).factorial : ZMod q) * hzero
  have hpos : 2 * (a : ZMod q) - 1 = -2 * 1 := by linear_combination hzero
  have hneg : -(6 * (a : ZMod q) + 1) = -2 * (-1) := by linear_combination -3 * hzero
  rw [← hq]
  simp only [← Int.modEq_and_modEq_iff_modEq_mul hcop, ← ZMod.intCast_eq_intCast_iff,
    Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_neg,
    Int.cast_add, ZMod.natCast_self, mul_zero, zero_sub, zero_add, hpos, hneg, hfac,
    ← and_or_left, ← Nat.prime_iff_fac_equiv_neg_one (show a ≠ 1 by omega)]

private theorem prime_iff_factorial_sign {a : ℕ} (ha : Odd a) :
    (2 * a + 1).Prime ↔ (a.factorial : ZMod (2 * a + 1)) = 1 ∨
      (a.factorial : ZMod (2 * a + 1)) = -1 := by
  have hw := Nat.prime_iff_fac_equiv_neg_one (n := 2 * a + 1) (show 2 * a + 1 ≠ 1 by
    obtain ⟨k, hk⟩ := ha
    omega)
  rw [ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq (show Odd (2 * a + 1) from ⟨a, rfl⟩),
    show (2 * a + 1 - 1) / 2 = a by omega, ha.neg_one_pow, neg_one_mul, neg_inj] at hw
  constructor
  · intro hp
    let : Fact (2 * a + 1).Prime := ⟨hp⟩
    exact sq_eq_one_iff.mp (hw.mp hp)
  · rintro (h | h) <;> exact hw.mpr (by simp [h])

end isSophieGermainPrime_ne_two_iff_factorial_modEq

open isSophieGermainPrime_ne_two_iff_factorial_modEq

/-- **Wilson-type characterization of Sophie Germain primes.** Let $a \ge 2$ be a natural number.
Then $a$ is a Sophie Germain prime other than $2$ if and only if
$(a - 1)! \equiv 2a - 1 \pmod{a(2a + 1)}$ or $(a - 1)! \equiv -(6a + 1) \pmod{a(2a + 1)}$, the
congruences being taken in the integers.

The paper states this for all positive integers $a$; at $a = 1$ the first congruence holds
($0! = 1 \equiv 1 \pmod 3$) while $1$ is not prime (the proof's appeal to Wilson's theorem modulo
$a$ needs $a \ge 2$).

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 5.3 (`integers-2025-A83-thm-5-3`). -/
public theorem isSophieGermainPrime_ne_two_iff_factorial_modEq {a : ℕ} (ha : 2 ≤ a) :
    (a.IsSophieGermainPrime ∧ a ≠ 2) ↔
      ((a - 1).factorial : ℤ) ≡ 2 * a - 1 [ZMOD a * (2 * a + 1)] ∨
        ((a - 1).factorial : ℤ) ≡ -(6 * a + 1) [ZMOD a * (2 * a + 1)] := by
  by_cases htwo : a = 2
  · subst a
    simp only [ne_self_iff_false, and_false, false_iff]
    decide
  rw [split_residues ha, Nat.isSophieGermainPrime_iff, and_iff_left htwo]
  exact and_congr_right fun hp => prime_iff_factorial_sign (hp.odd_of_ne_two htwo)

end MetaMathlibExt
