/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.SumTwoSquares

import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Rational solvability of the negative Pell equation

For a positive squarefree integer `d`, the equation `x² - d y² = -1` has a rational solution if
and only if no prime divisor of `d` is congruent to `3` modulo `4`
(`MetaMathlibExt.negPell_rat_solvable_iff`).

This is Theorem 5 of Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between
Planar Lines with Rational Slopes*, INTEGERS 24 (2024), Article A111, numbered as in its arXiv
version arXiv:2305.01091v20, which states it for squarefree `d > 1`. The case `d = 1` holds as
well: `(0, 1)` is a solution and `1` has no prime divisor.

## Proof

As in the source, both directions rest on the characterization of the natural numbers that are
sums of two squares (`Nat.eq_sq_add_sq_iff`).

* If no prime `p ≡ 3 (mod 4)` divides `d`, then `d = a² + b²` for natural numbers `a` and `b`, one
  of which, say `b`, is nonzero because `d > 0`; then `(a / b, 1 / b)` is a solution.
* Conversely, clearing the denominators of a rational solution gives natural numbers `A`, `B`, `C`
  with `A² + B² = d C²` and `B > 0`. Every prime `p ≡ 3 (mod 4)` divides this positive sum of two
  squares to an even power, while a prime divisor `p` of the squarefree number `d` divides `d C²`
  to the odd power `1 + 2 v_p(C)`.
-/

public section

namespace MetaMathlibExt

/-- **Rational solvability of the negative Pell equation.** For a positive squarefree integer
$d$, the equation $x^2 - d y^2 = -1$ has a rational solution if and only if no prime divisor of
$d$ is congruent to $3$ modulo $4$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 5 (`integers-2024-A111-thm-5`). -/
theorem negPell_rat_solvable_iff (d : ℕ) (hd : 0 < d) (hsq : Squarefree d) :
    (∃ x y : ℚ, x ^ 2 - d * y ^ 2 = -1) ↔ ∀ p : ℕ, p.Prime → p ∣ d → p % 4 ≠ 3 := by
  constructor
  · rintro ⟨x, y, h⟩ p hp hpd hp4
    have : Fact p.Prime := ⟨hp⟩
    -- Clear the denominators: `A² + B² = d C²` in `ℕ`, with `B > 0`.
    set A : ℕ := (x.num * y.den).natAbs with hA
    set B : ℕ := x.den * y.den with hB
    set C : ℕ := (y.num * x.den).natAbs with hC
    have hBpos : 0 < B := Nat.mul_pos x.den_pos y.den_pos
    have key : A ^ 2 + B ^ 2 = d * C ^ 2 := by
      have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
      have hy : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
      have hZ : ((A : ℤ) : ℚ) ^ 2 + ((B : ℤ) : ℚ) ^ 2 = d * ((C : ℤ) : ℚ) ^ 2 := by
        simp only [hA, hB, hC, Int.natCast_natAbs, Int.cast_abs, sq_abs, Int.cast_mul,
          Int.cast_natCast, Nat.cast_mul, hx, hy]
        linear_combination ((x.den : ℚ) * y.den) ^ 2 * h
      exact_mod_cast hZ
    have hn : d * C ^ 2 ≠ 0 := by
      rw [← key]
      exact (Nat.add_pos_right _ (pow_pos hBpos 2)).ne'
    have hC0 : C ≠ 0 := by
      rintro hC0
      simp [hC0] at hn
    -- `p ≡ 3 (mod 4)` divides the sum of two squares `d C²` to an even power ...
    have heven := Nat.eq_sq_add_sq_iff.mp ⟨A, B, key.symm⟩ p
      (Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_left hpd _, hn⟩) hp4
    rw [Nat.padicValNat_def, Nat.multiplicity_mul hd.ne' (pow_ne_zero 2 hC0),
      Nat.multiplicity_pow C 2] at heven
    -- ... but it divides the squarefree `d` exactly once.
    have h1 : multiplicity p d = 1 := by
      have hle : d.factorization p ≤ 1 := hsq.natFactorization_le_one p
      rw [Nat.factorization_def d hp] at hle
      have hge : 1 ≤ multiplicity p d := one_le_multiplicity_of_dvd hd.ne' hpd
      omega
    rw [h1] at heven
    obtain ⟨k, hk⟩ := heven
    omega
  · intro H
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, d = a ^ 2 + b ^ 2 :=
      Nat.eq_sq_add_sq_iff.mpr fun q hq hq4 =>
        absurd hq4 (H q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq))
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · -- `d = a²` with `a ≠ 0`: take `(x, y) = (0, 1 / a)`.
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hab
        omega
      refine ⟨0, 1 / a, ?_⟩
      rw [hab]
      push_cast
      field_simp
      ring
    · -- `b ≠ 0`: take `(x, y) = (a / b, 1 / b)`.
      refine ⟨a / b, 1 / b, ?_⟩
      rw [hab]
      push_cast
      field_simp
      ring

end MetaMathlibExt

end
