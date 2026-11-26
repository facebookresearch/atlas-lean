/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Int.ModEq

/-!
# Jacobi symbols of discriminants

For a discriminant, the Jacobi symbol at an odd prime depends only on the residue class of the prime
modulo the discriminant.
-/

namespace MetaMathlibExt

private theorem jacobiSym_swap_of_emod_four_eq_one {D : ℤ} (hD : D % 4 = 1)
    {p : ℕ} (hp : Odd p) : jacobiSym D p = jacobiSym p D.natAbs := by
  rcases Int.natAbs_eq D with h | h
  · have ha : D.natAbs % 4 = 1 := by omega
    conv_lhs => rw [h]
    exact jacobiSym.quadratic_reciprocity_one_mod_four ha hp
  · -- The sign from the negative numerator cancels the reciprocity sign.
    have ha : D.natAbs % 4 = 3 := by omega
    have haOdd : Odd D.natAbs := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three ha)
    have hsign : qrSign D.natAbs p = jacobiSym (-1) p := by
      rw [qrSign, ZMod.χ₄_nat_three_mod_four ha]
    conv_lhs => rw [h]
    rw [jacobiSym.neg _ hp, jacobiSym.quadratic_reciprocity' haOdd hp,
      qrSign.symm hp haOdd, ← jacobiSym.at_neg_one hp, ← hsign,
      ← mul_assoc, ← pow_two, qrSign.sq_eq_one haOdd hp, one_mul]

/-- **Jacobi symbols of a discriminant $D$ agree at odd primes congruent modulo $D$.** Let $p$ and
$p'$ be odd primes and let $D$ be an integer with $D \equiv 0$ or $1 \pmod 4$ that is coprime to
$p$. If $p' = p + D x$ for some integer $x$, then the Jacobi symbols agree:
$\left(\frac{D}{p'}\right) = \left(\frac{D}{p}\right)$.

For an odd prime $p$ the Jacobi symbol $\left(\frac{D}{p}\right)$ is the Legendre symbol and agrees
with the Kronecker symbol.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 1 (`integers-2026-A102-lem-1`). -/
public theorem jacobiSym_prime_add_mul_eq {p p' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp' : p'.Prime) (hp'2 : p' ≠ 2) {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hDp : IsCoprime D p) {x : ℤ} (hx : (p' : ℤ) = p + D * x) :
    jacobiSym D p' = jacobiSym D p := by
  by_cases hD0 : D = 0
  · subst D
    have heq : p' = p := by simpa using hx
    rw [heq]
  have ho := hp.eq_two_or_odd'.resolve_left hp2
  have ho' := hp'.eq_two_or_odd'.resolve_left hp'2
  have hmod : (p : ℤ) ≡ (p' : ℤ) [ZMOD D.natAbs] := by
    rw [Int.modEq_natAbs, Int.modEq_iff_dvd]
    exact ⟨x, by rw [hx, add_sub_cancel_left]⟩
  rcases hD with hD | hD
  · -- Removing the square factor 4 makes the period from `mod_right` equal to `|D|`.
    obtain ⟨d, rfl⟩ := Int.dvd_of_emod_eq_zero hD
    simp only [jacobiSym.mul_left, jacobiSym.at_four ho, jacobiSym.at_four ho', one_mul]
    have hm : p ≡ p' [MOD 4 * d.natAbs] := by
      apply Int.natCast_modEq_iff.mp
      simpa [Int.natAbs_mul] using hmod
    rw [jacobiSym.mod_right d ho', jacobiSym.mod_right d ho, ← hm]
  · rw [jacobiSym_swap_of_emod_four_eq_one hD ho', jacobiSym_swap_of_emod_four_eq_one hD ho]
    exact jacobiSym.mod_left' hmod.symm

end MetaMathlibExt
