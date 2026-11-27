/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer values of the generating function of `A_{n+1} = p A_n + A_{n-1}` at rational points

For integers `a`, `b`, `p`, the sequence with `A_0 = a`, `A_1 = b` and
`A_{n+1} = p A_n + A_{n-1}` has the generating function
`A(x) = (a (1 - p x) + b x) / (1 - p x - x ^ 2)`. This file defines its value at a rational number
and proves the integrality criterion at a rational point stated by Luu Ba Thang and Nguyen Duy
Nguyen, *Integer Values of Generating Functions for a Type of Second-Order Linear Recurrence
Sequence*, Journal of Integer Sequences 28 (2025), Article 25.8.3.

## Main definitions

* `MetaMathlibExt.secondOrderGenValue`: the value `A(x)` of the generating function at a rational
  number `x`.

## Main statements

* `MetaMathlibExt.secondOrderGenValue_integer_iff`: for `p ≠ 0` and coprime integers `r`, `s` with
  `s ≠ 0`, `A(r / s)` is an integer if and only if `b ≡ -a r t` modulo
  `D = s ^ 2 - p r s - r ^ 2` for every inverse `t` of `s` modulo `D`.

## Proof

As `r` and `s` are coprime, both are coprime to `D`, and `D ≠ 0` because `p ≠ 0`. Clearing
denominators gives `A(r / s) = s (a s - a p r + b r) / D`, and
`s (a s - a p r + b r) = r (b s + a r) + a D`. Hence `A(r / s)` is an integer exactly when `D`
divides `b s + a r`, which is the congruence `b ≡ -a r t` for an inverse `t` of `s` modulo `D`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generating function of the recurrence $A_{n+1} = pA_n + A_{n-1}$.** For integers $a$, $b$,
$p$ and a rational number $x$, $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$, with the convention
that a fraction with denominator $0$ is $0$. As a rational function, $A$ is the generating function
$\sum_{n \ge 0} A_n x^n$ of the sequence with $A_0 = a$, $A_1 = b$ and $A_{n+1} = pA_n + A_{n-1}$;
for $p \ne 0$ the denominator $1 - px - x^2$ has no rational root.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2. -/
def secondOrderGenValue (a b p : ℤ) (x : ℚ) : ℚ :=
  (a * (1 - p * x) + b * x) / (1 - p * x - x ^ 2)

/-- **Value of the generating function at zero.** For all integers $a, b, p$, the function
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ on the rationals satisfies $A(0) = a$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, proof of Theorem 2. -/
theorem secondOrderGenValue_zero (a b p : ℤ) : secondOrderGenValue a b p 0 = a := by
  simp [secondOrderGenValue]

/-- A quotient of integers is an integer exactly when the denominator divides the numerator. -/
private theorem exists_intCast_div_eq_iff {m n : ℤ} (hn : n ≠ 0) :
    (∃ z : ℤ, (m : ℚ) / n = z) ↔ n ∣ m := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · rintro ⟨z, hz⟩
    rw [div_eq_iff hnq] at hz
    exact ⟨z, by rw [mul_comm]; exact_mod_cast hz⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

/-- **Integrality criterion at a rational point.** Let $a, b, p$ be integers with $p \ne 0$ and let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$. Let $r, s$ be coprime integers
with $s \ne 0$ and put $D = s^2 - prs - r^2$. Then $A(r/s)$ is an integer if and only if
$b \equiv -art \pmod{D}$ for every integer $t$ with $st \equiv 1 \pmod{D}$.

Since $s$ is invertible modulo $D$, this is the congruence $b \equiv -ars^{-1} \pmod{|D|}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 4 (`jis-2025-25.8.3-lem-4`). -/
theorem secondOrderGenValue_integer_iff (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) :
    (∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) ↔
      ∀ t : ℤ, s * t ≡ 1 [ZMOD (s ^ 2 - p * r * s - r ^ 2)] →
        b ≡ -a * r * t [ZMOD (s ^ 2 - p * r * s - r ^ 2)] := by
  have hcop : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hrs
  -- `r` and `s` are both coprime to `D = s ^ 2 - p r s - r ^ 2`.
  have hrD : IsCoprime r (s ^ 2 - p * r * s - r ^ 2) := by
    convert hcop.pow_right (n := 2) |>.add_mul_left_right (-(p * s) - r) using 1
    ring
  have hsD : IsCoprime s (s ^ 2 - p * r * s - r ^ 2) := by
    convert ((IsCoprime.neg_right_iff s (r ^ 2)).mpr hcop.symm.pow_right).add_mul_left_right
      (s - p * r) using 1
    ring
  -- Hence `D ≠ 0`: otherwise `r` and `s` are units and `D = -p r s ≠ 0`.
  have hD : s ^ 2 - p * r * s - r ^ 2 ≠ 0 := by
    intro h0
    rw [h0] at hrD hsD
    rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hrD) with rfl | rfl <;>
      rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp hsD) with rfl | rfl <;>
      exact hp (by linarith)
  -- Clearing denominators: `A(r / s) = s (a s - a p r + b r) / D`.
  have hval : secondOrderGenValue a b p ((r : ℚ) / s) =
      ((s * (a * s - a * p * r + b * r) : ℤ) : ℚ) / ((s ^ 2 - p * r * s - r ^ 2 : ℤ) : ℚ) := by
    have hsq : (s : ℚ) ≠ 0 := by exact_mod_cast hs
    have hden : (1 - p * ((r : ℚ) / s) - ((r : ℚ) / s) ^ 2 : ℚ) =
        ((s ^ 2 - p * r * s - r ^ 2 : ℤ) : ℚ) / s ^ 2 := by
      push_cast
      field_simp
    have hDq : ((s ^ 2 - p * r * s - r ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD
    rw [secondOrderGenValue, hden]
    field_simp
    push_cast
    ring
  rw [hval, exists_intCast_div_eq_iff hD,
    show s * (a * s - a * p * r + b * r) =
      r * (b * s + a * r) + a * (s ^ 2 - p * r * s - r ^ 2) by ring,
    dvd_add_left (dvd_mul_left _ _), hrD.symm.dvd_mul_left_iff]
  constructor
  · intro h t ht
    rw [Int.modEq_iff_dvd] at ht ⊢
    rw [show -a * r * t - b = -t * (b * s + a * r) + -b * (1 - s * t) by ring]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right ht _)
  · intro h
    obtain ⟨u, v, huv⟩ := hsD
    have hu : s * u ≡ 1 [ZMOD (s ^ 2 - p * r * s - r ^ 2)] :=
      Int.modEq_iff_dvd.mpr ⟨v, by linear_combination -huv⟩
    have h2 := Int.modEq_iff_dvd.mp (h u hu)
    rw [show b * s + a * r = -s * (-a * r * u - b) + a * r * (1 - s * u) by ring]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hu) _)

end

end MetaMathlibExt
