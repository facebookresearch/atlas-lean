/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.KroneckerJacobiOdd

@[expose] public section

/-! `χ₄`-corrected reciprocity bridge at `D % 4 = 3` for odd denominators.

This strengthens the prime-denominator bridge to all odd natural denominators. -/

namespace MetaMathlibExt

/-- Sign identity for the positive `D % 4 = 3` case: when `N % 4 = 3`,
`N / 2` is odd, so the `qrSign` exponent takes the parity of `p / 2`,
which is exactly `χ₄ p`. -/
private theorem qrSign_eq_chi4_of_N_three_mod_four (p N : ℕ) (hp_odd : Odd p)
    (hNodd : Odd N) (hN3 : N % 4 = 3) : qrSign p N = ZMod.χ₄ p := by
  have hp14 : p % 4 = 1 ∨ p % 4 = 3 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp hp_odd
    omega
  cases hp14 with
  | inl hp1 =>
    have hc1 : ZMod.χ₄ p = 1 := ZMod.χ₄_nat_one_mod_four hp1
    have hqr : qrSign p N = (-1 : ℤ) ^ (p / 2 * (N / 2)) :=
      qrSign.neg_one_pow hp_odd hNodd
    have hp2mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
    have h4p : 4 * (p / 4) + p % 4 = p := Nat.div_add_mod p 4
    have h2p : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
    have hEvenHalf : Even (p / 2) := ⟨p / 4, by omega⟩
    have hEvenExp : Even (p / 2 * (N / 2)) := hEvenHalf.mul_right _
    rw [hqr, hc1, hEvenExp.neg_one_pow]
  | inr hp3 =>
    have hc3 : ZMod.χ₄ p = -1 := ZMod.χ₄_nat_three_mod_four hp3
    have hqr : qrSign p N = (-1 : ℤ) ^ (p / 2 * (N / 2)) :=
      qrSign.neg_one_pow hp_odd hNodd
    have hp2mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
    have hN2mod : N % 2 = 1 := Nat.odd_iff.mp hNodd
    have h4p : 4 * (p / 4) + p % 4 = p := Nat.div_add_mod p 4
    have h2p : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
    have h4N : 4 * (N / 4) + N % 4 = N := Nat.div_add_mod N 4
    have h2N : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
    have hPodd : Odd (p / 2) := ⟨p / 4, by omega⟩
    have hNoddHalf : Odd (N / 2) := ⟨N / 4, by omega⟩
    have hOddExp : Odd (p / 2 * (N / 2)) := hPodd.mul hNoddHalf
    rw [hqr, hc3, hOddExp.neg_one_pow]

/-- **Kronecker symbol at odd numbers for integers congruent to 3 mod 4.** Let $\chi_4$ be the
nontrivial Dirichlet character modulo $4$, so $\chi_4(n) = 1$ for $n \equiv 1 \pmod 4$ and
$\chi_4(n) = -1$ for $n \equiv 3 \pmod 4$. Let $D$ be an integer with $D \equiv 3 \pmod 4$ and
let $p$ be an odd natural number. Then $\chi_4(p) \cdot \left(\frac{p}{|D|}\right) =
\left(\frac{D}{p}\right)$, where $\left(\frac{p}{|D|}\right)$ is the Jacobi symbol and
$\left(\frac{D}{p}\right)$ is the Kronecker symbol.

For $D > 0$ the factor $\chi_4(p)$ is the sign from quadratic reciprocity; for $D < 0$ it is
the value $\left(\frac{-1}{p}\right) = \chi_4(p)$. -/
public theorem chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four
    (D : ℤ) (p : ℕ) (hp_odd : Odd p) (h3 : D % 4 = 3) :
    (ZMod.χ₄ p : ℤ) * jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
  have hDne : D ≠ 0 := by omega
  have hKR : kroneckerSym D p = jacobiSym D p :=
    kroneckerSym_eq_jacobiSym_of_odd D p hp_odd
  by_cases hpos : 0 < D
  · have hcast : ((D.natAbs : ℕ) : ℤ) = D := by
      rw [Int.natCast_natAbs, abs_of_pos hpos]
    have hNmod : D.natAbs % 4 = 3 := by omega
    have hNodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
    have hrec : jacobiSym ((D.natAbs : ℕ) : ℤ) p =
        qrSign p D.natAbs * jacobiSym ((p : ℕ) : ℤ) D.natAbs := by
      exact jacobiSym.quadratic_reciprocity' hNodd hp_odd
    have hsign : qrSign p D.natAbs = ZMod.χ₄ p :=
      qrSign_eq_chi4_of_N_three_mod_four p D.natAbs hp_odd hNodd hNmod
    have hDrewrite : jacobiSym D p = jacobiSym ((D.natAbs : ℕ) : ℤ) p := by
      rw [hcast]
    rw [hKR, hDrewrite, hrec, hsign]
  · have hneg : D < 0 := by omega
    have hDneg : ((D.natAbs : ℕ) : ℤ) = -D := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
    have hDeq2 : D = (-1 : ℤ) * ((D.natAbs : ℕ) : ℤ) := by omega
    have hNmod : D.natAbs % 4 = 1 := by omega
    have hNodd : Odd D.natAbs := Nat.odd_iff.mpr (by omega)
    have hDsplit : jacobiSym D p
        = jacobiSym (-1) p * jacobiSym ((D.natAbs : ℕ) : ℤ) p := by
      conv_lhs => rw [hDeq2]
      rw [jacobiSym.mul_left]
    have hneg1 : jacobiSym (-1) p = ZMod.χ₄ p := by
      exact jacobiSym.at_neg_one hp_odd
    have hrec : jacobiSym ((D.natAbs : ℕ) : ℤ) p
        = jacobiSym ((p : ℕ) : ℤ) D.natAbs := by
      exact jacobiSym.quadratic_reciprocity_one_mod_four hNmod hp_odd
    rw [hKR, hDsplit, hneg1, hrec]

end MetaMathlibExt

end
