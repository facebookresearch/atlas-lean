/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.QuadraticReciprocityBridge

@[expose] public section

/-! Negative `D % 4 = 1` branch of the reciprocity bridge. -/

namespace MetaMathlibExt

/-- **Kronecker symbol at odd primes for negative integers congruent to 1 mod 4.** Let $D$ be a
negative integer with $D \equiv 1 \pmod 4$ and let $p$ be an odd prime. Then the Jacobi symbol
$\left(\frac{p}{|D|}\right)$ equals the Kronecker symbol $\left(\frac{D}{p}\right)$. -/
public theorem jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg
    (D : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hneg : D < 0)
    (h1 : D % 4 = 1) :
    jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hDneg : ((D.natAbs : ℕ) : ℤ) = -D := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
  have hDeq2 : D = (-1 : ℤ) * ((D.natAbs : ℕ) : ℤ) := by
    omega
  have hNmod : D.natAbs % 4 = 3 := by
    omega
  have hNodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
  have hKR : kroneckerSym D p = jacobiSym D p :=
    kroneckerSym_eq_jacobiSym_of_prime_ne_two D p hp hp2
  have hDsplit : jacobiSym D p =
      jacobiSym (-1) p * jacobiSym ((D.natAbs : ℕ) : ℤ) p := by
    conv_lhs => rw [hDeq2]
    rw [jacobiSym.mul_left]
  have hneg1 : jacobiSym (-1) p = ZMod.χ₄ p := by
    exact jacobiSym.at_neg_one hp_odd
  have hrec : jacobiSym ((D.natAbs : ℕ) : ℤ) p =
      qrSign p D.natAbs * jacobiSym ((p : ℕ) : ℤ) D.natAbs := by
    exact jacobiSym.quadratic_reciprocity' hNodd hp_odd
  have hcancel : ZMod.χ₄ p * qrSign p D.natAbs = 1 := by
    have hp14 : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp hp_odd
      omega
    cases hp14 with
    | inl hp1 =>
      have hc1 : ZMod.χ₄ p = 1 :=
        ZMod.χ₄_nat_one_mod_four hp1
      have hq1 : qrSign p D.natAbs = 1 := by
        have hqr := qrSign.neg_one_pow hp_odd hNodd
        have hp2mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
        have h4p : 4 * (p / 4) + p % 4 = p :=
          Nat.div_add_mod p 4
        have h2p : 2 * (p / 2) + p % 2 = p :=
          Nat.div_add_mod p 2
        have hEvenHalf : Even (p / 2) := ⟨p / 4, by omega⟩
        have hEvenExp : Even (p / 2 * (D.natAbs / 2)) :=
          hEvenHalf.mul_right _
        rw [hqr, hEvenExp.neg_one_pow]
      rw [hc1, hq1, mul_one]
    | inr hp3 =>
      have hc3 : ZMod.χ₄ p = -1 :=
        ZMod.χ₄_nat_three_mod_four hp3
      have hq3 : qrSign p D.natAbs = -1 := by
        have hqr := qrSign.neg_one_pow hp_odd hNodd
        have hp2mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
        have hN2mod : D.natAbs % 2 = 1 := Nat.odd_iff.mp hNodd
        have h4p : 4 * (p / 4) + p % 4 = p :=
          Nat.div_add_mod p 4
        have h2p : 2 * (p / 2) + p % 2 = p :=
          Nat.div_add_mod p 2
        have h4N : 4 * (D.natAbs / 4) + D.natAbs % 4 = D.natAbs :=
          Nat.div_add_mod D.natAbs 4
        have h2N : 2 * (D.natAbs / 2) + D.natAbs % 2 = D.natAbs :=
          Nat.div_add_mod D.natAbs 2
        have hPodd : Odd (p / 2) := ⟨p / 4, by omega⟩
        have hNoddHalf : Odd (D.natAbs / 2) := ⟨D.natAbs / 4, by omega⟩
        have hOddExp : Odd (p / 2 * (D.natAbs / 2)) :=
          hPodd.mul hNoddHalf
        rw [hqr, hOddExp.neg_one_pow]
      rw [hc3, hq3]
      decide
  rw [hKR, hDsplit, hneg1, hrec, ← mul_assoc, hcancel, one_mul]

/-- **Kronecker symbol at odd primes for integers congruent to 1 mod 4.** Let $D$ be an integer
with $D \equiv 1 \pmod 4$ and let $p$ be an odd prime. Then the Jacobi symbol
$\left(\frac{p}{|D|}\right)$ equals the Kronecker symbol $\left(\frac{D}{p}\right)$.

This covers $D$ of either sign. The congruence condition cannot be dropped: for $D = 3$ and
$p = 7$ the Jacobi symbol is $1$ while the Kronecker symbol is $-1$. -/
public theorem jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four
    (D : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h1 : D % 4 = 1) :
    jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
  rcases lt_trichotomy D 0 with hneg | rfl | hpos
  · exact jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg
      D p hp hp2 hneg h1
  · omega
  · exact jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
      D p hp hp2 hpos h1

end MetaMathlibExt

end
