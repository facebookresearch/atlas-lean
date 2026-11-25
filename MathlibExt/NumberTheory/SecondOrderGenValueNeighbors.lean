/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SecondOrderGenValue
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Neighbours of an integer value of a second-order generating function

For a nonzero recurrence coefficient, an integer value of the generating function at a reduced
fraction propagates to both neighbouring fractions when their denominators are nonzero.
-/

namespace MetaMathlibExt

/-- **Neighbours of an integer value.** Let $a, b, p$ be integers with $p \ne 0$ and let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$. If $r, s$ are coprime integers
with $r \ne 0$, $s \ne 0$ and $r + ps \ne 0$, and $A(r/s)$ is an integer, then $A(s/(r + ps))$
and $A((s - pr)/r)$ are integers.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 6 (`jis-2025-25.8.3-lem-6`). -/
public theorem secondOrderGenValue_neighbors_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hr : r ≠ 0)
    (hs : s ≠ 0) (hrps : r + p * s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) :
    (∃ z : ℤ, secondOrderGenValue a b p ((s : ℚ) / (r + p * s)) = z) ∧
      ∃ z : ℤ, secondOrderGenValue a b p (((s : ℚ) - p * r) / r) = z := by
  let D := s ^ 2 - p * r * s - r ^ 2
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr hrs
  -- Fix an inverse of the central denominator s modulo D.
  have hsD : IsCoprime s D := by
    convert ((IsCoprime.neg_right_iff s (r ^ 2)).mpr hcop.symm.pow_right).add_mul_left_right
      (s - p * r) using 1
    dsimp [D]
    ring
  obtain ⟨i, j, hij⟩ := hsD
  have hi : s * i ≡ 1 [ZMOD D] :=
    Int.modEq_iff_dvd.mpr ⟨j, by linear_combination -hij⟩
  have hb : b ≡ -a * r * i [ZMOD D] :=
    (secondOrderGenValue_integer_iff a b p hp r s hs hrs).mp hint i hi
  -- Both neighbours have modulus -D and represent the same fraction modulo D.
  have transfer (u v : ℤ) (hv : v ≠ 0) (huv : IsCoprime u v)
      (hD : v ^ 2 - p * u * v - u ^ 2 = -D) (hcross : r * v ≡ s * u [ZMOD D]) :
      ∃ z : ℤ, secondOrderGenValue a b p ((u : ℚ) / v) = z := by
    apply (secondOrderGenValue_integer_iff a b p hp u v hv
      (Int.isCoprime_iff_gcd_eq_one.mp huv)).mpr
    simp only [hD, Int.modEq_neg]
    intro t ht
    have hratio : r * i ≡ u * t [ZMOD D] := calc
      r * i ≡ r * i * (v * t) [ZMOD D] := by simpa only [mul_one] using ht.symm.mul_left (r * i)
      _ ≡ u * t * (s * i) [ZMOD D] := by
        convert hcross.mul_right (i * t) using 1 <;> ring
      _ ≡ u * t [ZMOD D] := by simpa only [mul_one] using hi.mul_left (u * t)
    exact hb.trans (by simpa only [mul_assoc] using hratio.mul_left (-a))
  constructor
  · rw [← Int.cast_mul, ← Int.cast_add]
    apply transfer s (r + p * s) hrps (hcop.symm.add_mul_right_right p)
    · dsimp [D]
      ring
    · exact Int.modEq_iff_dvd.mpr ⟨1, by dsimp [D]; ring⟩
  · rw [← Int.cast_mul, ← Int.cast_sub]
    apply transfer (s - p * r) r hr (by simpa using hcop.symm)
    · dsimp [D]
      ring
    · exact Int.modEq_iff_dvd.mpr ⟨1, by dsimp [D]; ring⟩

end MetaMathlibExt
