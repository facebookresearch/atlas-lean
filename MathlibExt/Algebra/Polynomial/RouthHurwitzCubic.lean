/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic

import Mathlib.FieldTheory.IsRealClosed.Real
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Basic

/-!
# Routh–Hurwitz criterion for cubic polynomials

We factor a monic real cubic at a real root and use the sum and product of the two roots of
its real quadratic factor to test their real parts.

## References

* K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*,
  2nd ed., Princeton University Press, 2021. In the authors' electronic edition v3.1.5,
  see §2.2, p. 2-10, condition (2.18):
  <https://www.cds.caltech.edu/~murray/books/AM08/pdf/fbs-principles_24Jul2020.pdf>.
-/

namespace MetaMathlibExt

/-- A real scalar has a complex square root, real or purely imaginary according to its sign. -/
private theorem exists_sq_eq_ofReal (d : ℝ) : ∃ v : ℂ, v ^ 2 = (d : ℂ) := by
  obtain ⟨u, hu⟩ | ⟨u, hu⟩ := IsRealClosed.isSquare_or_isSquare_neg d
  · exact ⟨(u : ℂ), by rw [sq, ← Complex.ofReal_mul, ← hu]⟩
  · refine ⟨Complex.I * (u : ℂ), ?_⟩
    rw [mul_pow, Complex.I_sq, sq, ← Complex.ofReal_mul, ← hu, Complex.ofReal_neg]
    ring

/-- A monic real quadratic has both roots in the open left half-plane exactly when both
non-leading coefficients are positive. -/
private theorem quadratic_neg_re_iff (b c : ℝ) :
    (∀ z : ℂ, z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 → z.re < 0) ↔ 0 < b ∧ 0 < c := by
  obtain ⟨v, hv⟩ := exists_sq_eq_ofReal (b ^ 2 - 4 * c)
  push_cast at hv
  let z : ℂ := (-(b : ℂ) + v) / 2
  let w : ℂ := (-(b : ℂ) - v) / 2
  have hsum : z + w = -(b : ℂ) := by
    dsimp [z, w]
    ring
  have hprod : z * w = (c : ℂ) := by
    dsimp [z, w]
    linear_combination -hv / 4
  have hfactor (t : ℂ) : t ^ 2 + (b : ℂ) * t + (c : ℂ) = (t - z) * (t - w) := by
    linear_combination t * hsum - hprod
  have hreSum : z.re + w.re = -b := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] using congrArg Complex.re hsum
  have hwim : w.im = -z.im := by
    have him := congrArg Complex.im hsum
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero] at him
    linarith
  have hreProd : z.re * w.re + z.im ^ 2 = c := by
    simpa only [Complex.mul_re, Complex.ofReal_re, hwim, mul_neg, sub_neg_eq_add, pow_two]
      using congrArg Complex.re hprod
  constructor
  · intro h
    have hz : z.re < 0 := h z (by rw [hfactor, sub_self, zero_mul])
    have hw : w.re < 0 := h w (by rw [hfactor, sub_self, mul_zero])
    refine ⟨by linarith, ?_⟩
    rw [← hreProd]
    exact add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg hz hw) (sq_nonneg _)
  · rintro ⟨hb, hc⟩ t ht
    have hneg : z.re < 0 ∧ w.re < 0 := by
      by_cases him : z.im = 0
      · have hpos : 0 < z.re * w.re := by
          rw [← hreProd] at hc
          simpa [him] using hc
        rcases mul_pos_iff.mp hpos with ⟨hz, hw⟩ | ⟨hz, hw⟩
        · exfalso
          linarith
        · exact ⟨hz, hw⟩
      · have himProd : z.im * (w.re - z.re) = 0 := by
          have heq := congrArg Complex.im hprod
          simp only [Complex.mul_im, Complex.ofReal_im, hwim] at heq
          linear_combination heq
        have heq : w.re = z.re := sub_eq_zero.mp ((mul_eq_zero.mp himProd).resolve_left him)
        rw [heq] at hreSum ⊢
        have hz : z.re < 0 := by linarith
        exact ⟨hz, hz⟩
    rcases mul_eq_zero.mp ((hfactor t).symm.trans ht) with htz | htw
    · rw [sub_eq_zero.mp htz]
      exact hneg.1
    · rw [sub_eq_zero.mp htw]
      exact hneg.2

/-- **Strict Routh–Hurwitz criterion for a monic real cubic.** All complex roots of
`z^3 + a₂ z^2 + a₁ z + a₀` have strictly negative real part if and only if
`0 < a₂`, `0 < a₀`, and `a₀ < a₂ * a₁`. These inequalities imply `0 < a₁`,
which Åström–Murray state separately in condition (2.18).

Factor at a real root `-r` as `(z + r)(z² + b z + c)`. The root condition becomes
`r, b, c > 0`, and `a₂ * a₁ - a₀ = b * (r * (r + b) + c)`. In the converse,
positive coefficients force `-r < 0`; the product and the determinant then give `c, b > 0`. -/
public theorem routhHurwitzCubic_iff (a₀ a₁ a₂ : ℝ) :
    (∀ z : ℂ, z ^ 3 + (a₂ : ℂ) * z ^ 2 + (a₁ : ℂ) * z + (a₀ : ℂ) = 0 → z.re < 0) ↔
      0 < a₂ ∧ 0 < a₀ ∧ a₀ < a₂ * a₁ := by
  let p : Polynomial ℝ := .X ^ 3 + (.C a₂ * .X ^ 2 + .C a₁ * .X) + .C a₀
  have hp : p.natDegree = 3 := by
    have h₁ : (Polynomial.C a₁ * Polynomial.X).natDegree ≤ 2 :=
      (by simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le a₁ 1 :
        (Polynomial.C a₁ * Polynomial.X).natDegree ≤ 1).trans (by decide)
    have h₂ : (Polynomial.C a₂ * Polynomial.X ^ 2 + Polynomial.C a₁ * Polynomial.X).natDegree
        ≤ 2 := Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_C_mul_X_pow_le a₂ 2) h₁
    dsimp only [p]
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_X_pow]
    exact h₂.trans_lt (by decide)
  obtain ⟨x, hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := p) (by rw [hp]; decide)
  let r : ℝ := -x
  let b : ℝ := a₂ - r
  let c : ℝ := a₁ - r * b
  have hroot : (-r) ^ 3 + a₂ * (-r) ^ 2 + a₁ * (-r) + a₀ = 0 := by
    simpa [p, r, Polynomial.IsRoot, add_assoc] using hx
  have h₂ : a₂ = r + b := by dsimp [b]; ring
  have h₁ : a₁ = r * b + c := by dsimp [c]; ring
  have h₀ : a₀ = r * c := by
    dsimp only [c, b]
    linear_combination hroot
  have hfactor (z : ℂ) :
      z ^ 3 + (a₂ : ℂ) * z ^ 2 + (a₁ : ℂ) * z + (a₀ : ℂ) =
        (z + (r : ℂ)) * (z ^ 2 + (b : ℂ) * z + (c : ℂ)) := by
    rw [h₂, h₁, h₀]
    push_cast
    ring
  have hdet : a₂ * a₁ - a₀ = b * (r * (r + b) + c) := by
    rw [h₂, h₁, h₀]
    ring
  constructor
  · intro h
    have hr : 0 < r := by
      have hneg := h (-(r : ℂ)) (by rw [hfactor, neg_add_cancel, zero_mul])
      simpa only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero] using hneg
    have ⟨hb, hc⟩ := (quadratic_neg_re_iff b c).mp fun z hz ↦ h z (by rw [hfactor, hz, mul_zero])
    refine ⟨by rw [h₂]; positivity, by rw [h₀]; positivity, sub_pos.mp ?_⟩
    rw [hdet]
    positivity
  · rintro ⟨ha₂, ha₀, hlt⟩
    have ha₁ : 0 < a₁ := pos_of_mul_pos_right (ha₀.trans hlt) ha₂.le
    have hr : 0 < r := by
      by_contra! hn
      have hn' : 0 ≤ -r := neg_nonneg.mpr hn
      have hpos : 0 < (-r) ^ 3 + a₂ * (-r) ^ 2 + a₁ * (-r) + a₀ := by positivity
      exact (ne_of_gt hpos) hroot
    have hc : 0 < c := pos_of_mul_pos_right (h₀ ▸ ha₀) hr.le
    have hq : 0 < r * (r + b) + c := by rw [← h₂]; positivity
    have hb : 0 < b := pos_of_mul_pos_left (hdet ▸ sub_pos.mpr hlt) hq.le
    intro z hz
    rcases mul_eq_zero.mp ((hfactor z).symm.trans hz) with hlin | hquad
    · rw [eq_neg_of_add_eq_zero_left hlin, Complex.neg_re, Complex.ofReal_re]
      exact neg_lt_zero.mpr hr
    · exact (quadratic_neg_re_iff b c).mpr ⟨hb, hc⟩ z hquad

end MetaMathlibExt
