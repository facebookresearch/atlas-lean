/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Integer values along a second-order recurrence family

The recurrence step preserves coprimality and negates the integral denominator. For a coprime
pair `(r, s)`, divisibility of `b * s + a * r` by that denominator propagates in both directions,
even at a pair with a zero coordinate.
-/

namespace MetaMathlibExt

private def recurrenceDenom (p r s : ℤ) : ℤ := s ^ 2 - p * r * s - r ^ 2

private theorem isCoprime_recurrenceDenom {p r s : ℤ} (h : IsCoprime r s) :
    IsCoprime s (recurrenceDenom p r s) := by
  convert ((IsCoprime.neg_right_iff s (r ^ 2)).mpr h.symm.pow_right).add_mul_left_right
    (s - p * r) using 1
  unfold recurrenceDenom
  ring

private theorem integer_iff_dvd_linear {a b p r s : ℤ} (hp : p ≠ 0) (hs : s ≠ 0)
    (hc : IsCoprime r s) :
    (∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) ↔
      recurrenceDenom p r s ∣ b * s + a * r := by
  rw [secondOrderGenValue_integer_iff a b p hp r s hs (Int.isCoprime_iff_gcd_eq_one.mp hc)]
  let D := recurrenceDenom p r s
  change (∀ t : ℤ, s * t ≡ 1 [ZMOD D] → b ≡ -a * r * t [ZMOD D]) ↔ D ∣ b * s + a * r
  constructor
  · intro h
    obtain ⟨t, u, htu⟩ := isCoprime_recurrenceDenom (p := p) hc
    have ht : D ∣ 1 - s * t := ⟨u, by dsimp [D]; linear_combination -htu⟩
    have hb := Int.modEq_iff_dvd.mp (h t (Int.modEq_iff_dvd.mpr ht))
    rw [show b * s + a * r = -s * (-a * r * t - b) + a * r * (1 - s * t) by ring]
    exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right ht _)
  · intro h t ht
    rw [Int.modEq_iff_dvd] at ht ⊢
    rw [show -a * r * t - b = -t * (b * s + a * r) - b * (1 - s * t) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right ht _)

private def FamilyInvariant (a b p r s : ℤ) : Prop :=
  IsCoprime r s ∧ recurrenceDenom p r s ∣ b * s + a * r

private theorem familyInvariant_step (a b p r s : ℤ) :
    FamilyInvariant a b p s (p * s + r) ↔ FamilyInvariant a b p r s := by
  have hcop : IsCoprime s (p * s + r) ↔ IsCoprime r s := by
    rw [add_comm (p * s) r, IsCoprime.add_mul_right_right_iff, isCoprime_comm]
  have hD : recurrenceDenom p s (p * s + r) = -recurrenceDenom p r s := by
    unfold recurrenceDenom
    ring
  simp only [FamilyInvariant, hD, neg_dvd, hcop]
  refine and_congr_right fun hc => ?_
  -- We can cancel the shared coordinate `s` from divisibility even when `s = 0`:
  -- in that case coprimality forces the modulus to be a unit.
  have hcancel {z : ℤ} (h : recurrenceDenom p r s ∣ s * z) : recurrenceDenom p r s ∣ z :=
    (isCoprime_recurrenceDenom hc).symm.dvd_mul_left_iff.mp h
  constructor
  · intro h
    apply hcancel
    rw [show s * (b * s + a * r) = r * (b * (p * s + r) + a * s) +
      b * recurrenceDenom p r s by unfold recurrenceDenom; ring]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
  · intro h
    apply hcancel
    rw [show s * (b * (p * s + r) + a * s) = (p * s + r) * (b * s + a * r) +
      a * recurrenceDenom p r s by unfold recurrenceDenom; ring]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)

/-- **Integer values propagate along a family.** Let $a, b, p$ be integers with $p \ne 0$, let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $r, s$ let
$A^{(r,s)}$ be the two-sided integer sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all integers $n$. If $r$ and $s$ are
coprime integers with $s \ne 0$ and $A(r/s)$ is an integer, then
$A(A^{(r,s)}_n / A^{(r,s)}_{n+1})$ is an integer for every integer $n$ with
$A^{(r,s)}_{n+1} \ne 0$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1 (`jis-2025-25.8.3-thm-1`). -/
public theorem secondOrderGenValue_family_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (n : ℤ) (hn : secondOrderBiSeq p r s (n + 1) ≠ 0) :
    ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p r s n : ℚ) / secondOrderBiSeq p r s (n + 1)) = z := by
  let U := secondOrderBiSeq p r s
  let P (i : ℤ) := FamilyInvariant a b p (U i) (U (i + 1))
  have hc := Int.isCoprime_iff_gcd_eq_one.mpr hrs
  have hzero : P 0 := by
    simpa only [P, U, zero_add, secondOrderBiSeq_zero, secondOrderBiSeq_one] using
      (show FamilyInvariant a b p r s from ⟨hc, (integer_iff_dvd_linear hp hs hc).mp hint⟩)
  have hstep (i : ℤ) : P (i + 1) ↔ P i := by
    simp only [P, add_assoc, one_add_one_eq_two]
    rw [show U (i + 2) = p * U (i + 1) + U i from secondOrderBiSeq_add_two p r s i]
    exact familyInvariant_step a b p _ _
  have h : P n := Int.inductionOn' (motive := P) n 0 hzero (fun i _ => (hstep i).2)
    (fun i _ ih => (hstep (i - 1)).1 (by simpa only [sub_add_cancel] using ih))
  exact (integer_iff_dvd_linear hp hn h.1).2 h.2

end MetaMathlibExt
