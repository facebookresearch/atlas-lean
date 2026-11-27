/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ComputeDegree
import MathlibExt.Algebra.Polynomial.ReciprocalZeroOneFirstOddExponent

/-! # Tests for the first odd exponent of a reciprocal 0,1-polynomial -/

namespace MathlibExtTest.ReciprocalZeroOneFirstOddExponent

open Polynomial MathlibExt.Algebra.PalindromicZeroOneWanted

-- `X + 2` is not reciprocal: its reversal `2 X + 1` has constant term `1`.
example : ¬ IsReciprocalPoly (X + C 2 : ℤ[X]) := by
  intro h
  have h0 := congrArg (fun p : ℤ[X] => p.coeff 0) h
  simp only [coeff_zero_reverse, leadingCoeff_X_add_C, coeff_add, coeff_X_zero, coeff_C_zero,
    zero_add] at h0
  omega

-- `X` is not cyclotomic: every cyclotomic polynomial has constant term `1` or `-1`.
example : IsNoncyclotomic (X : ℤ[X]) := by
  intro n hn h
  have h0 := congrArg (fun p : ℤ[X] => p.coeff 0) h
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · simp [cyclotomic_coeff_zero ℤ h1] at h0
  · obtain rfl : n = 1 := by omega
    simp at h0

-- Under the hypotheses of the lemma, `f` has degree at least `6`.
example (f fe fo : ℤ[X]) (m l : ℕ)
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f)
    (hrec : IsReciprocalPoly f) (hnc : IsNoncyclotomic f)
    (hdeg : f.natDegree = 2 * m)
    (hdecomp : f = fe.comp (X ^ 2) + X ^ l * fo.comp (X ^ 2))
    (hfe : fe.natDegree = m) (hfo : fo.natDegree = m - l)
    (hl : Odd l) (hl0 : 0 < l)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    6 ≤ f.natDegree := by
  obtain ⟨-, -, h⟩ :=
    l_eq_min_support_and_lt f fe fo m l h01 hirr hrec hnc hdeg hdecomp hfe hfo hl hl0 hred
  omega

private theorem cyclotomic_five_eq : cyclotomic 5 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  simp [cyclotomic_prime, Finset.sum_range_succ]

private theorem natDegree_cyclotomic_five : (cyclotomic 5 ℤ).natDegree = 2 * 2 := by
  rw [natDegree_cyclotomic, Nat.totient_prime Nat.prime_five]

/- The fifth cyclotomic polynomial `1 + x + x^2 + x^3 + x^4` satisfies every hypothesis of the
lemma except non-cyclotomicity, with `m = 2`, `l = 1`, `f_e = 1 + x + x^2` and `f_o = 1 + x`,
while `2 * l < m` fails. So the lemma shows that it is not non-cyclotomic: that hypothesis
cannot be dropped. This is the boundary case `m = 2 * l` of the proof. -/
example : ¬ IsNoncyclotomic (cyclotomic 5 ℤ) := by
  intro hnc
  have hirr₅ := cyclotomic.irreducible (n := 5) (by norm_num)
  have hirr₁₀ := cyclotomic.irreducible (n := 10) (by norm_num)
  have h01 : IsZeroOnePoly (cyclotomic 5 ℤ) := by
    intro n
    rw [cyclotomic_five_eq]
    rcases n with _ | _ | _ | _ | _ | n <;> simp [coeff_X_pow, coeff_X, coeff_one]
  have hrec : IsReciprocalPoly (cyclotomic 5 ℤ) := by
    unfold IsReciprocalPoly
    ext n
    rw [coeff_reverse, natDegree_cyclotomic_five]
    rcases le_or_gt n (2 * 2) with hn | hn
    · rw [revAt_le hn, cyclotomic_five_eq]
      interval_cases n <;> simp [coeff_X_pow, coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt hn]
  have hdecomp : cyclotomic 5 ℤ =
      (1 + X + X ^ 2 : ℤ[X]).comp (X ^ 2) + X ^ 1 * (1 + X : ℤ[X]).comp (X ^ 2) := by
    rw [cyclotomic_five_eq]
    simp only [add_comp, one_comp, X_comp, pow_comp]
    ring
  have hfe : (1 + X + X ^ 2 : ℤ[X]).natDegree = 2 := by compute_degree!
  have hfo : (1 + X : ℤ[X]).natDegree = 2 - 1 := by compute_degree!
  have hred : ¬ Irreducible ((cyclotomic 5 ℤ).comp (X ^ 2)) := by
    intro hirr
    have hfactor : (cyclotomic 5 ℤ).comp (X ^ 2) = cyclotomic 10 ℤ * cyclotomic 5 ℤ := by
      simpa only [expand_eq_comp_X_pow] using
        cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (n := 5) (by norm_num) ℤ
    exact (hirr.isUnit_or_isUnit hfactor).elim hirr₁₀.not_isUnit hirr₅.not_isUnit
  have h := (l_eq_min_support_and_lt _ _ _ 2 1 h01 hirr₅ hrec hnc natDegree_cyclotomic_five
    hdecomp hfe hfo odd_one one_pos hred).2.2
  omega

private theorem natDegree_cyclotomic_three : (cyclotomic 3 ℤ).natDegree = 2 * 1 := by
  rw [natDegree_cyclotomic, Nat.totient_prime Nat.prime_three]

/- The third cyclotomic polynomial `1 + x + x^2` likewise satisfies every hypothesis of the
lemma except non-cyclotomicity, with `m = l = 1`, `f_e = 1 + x` and the constant odd part
`f_o = 1`, while `2 * l < m` fails. This is the other boundary case of the proof, `m = l`;
here `f(x^2) = Φ₆(x) Φ₃(x)` is reducible. -/
example : ¬ IsNoncyclotomic (cyclotomic 3 ℤ) := by
  intro hnc
  have hirr₃ := cyclotomic.irreducible (n := 3) (by norm_num)
  have hirr₆ := cyclotomic.irreducible (n := 6) (by norm_num)
  have h01 : IsZeroOnePoly (cyclotomic 3 ℤ) := by
    intro n
    rw [cyclotomic_three]
    rcases n with _ | _ | _ | n <;> simp [coeff_X_pow, coeff_X, coeff_one]
  have hrec : IsReciprocalPoly (cyclotomic 3 ℤ) := by
    unfold IsReciprocalPoly
    ext n
    rw [coeff_reverse, natDegree_cyclotomic_three]
    rcases le_or_gt n (2 * 1) with hn | hn
    · rw [revAt_le hn, cyclotomic_three]
      interval_cases n <;> simp [coeff_X_pow, coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt hn]
  have hdecomp : cyclotomic 3 ℤ =
      (1 + X : ℤ[X]).comp (X ^ 2) + X ^ 1 * (1 : ℤ[X]).comp (X ^ 2) := by
    rw [cyclotomic_three]
    simp only [add_comp, one_comp, X_comp]
    ring
  have hfe : (1 + X : ℤ[X]).natDegree = 1 := by compute_degree!
  have hfo : (1 : ℤ[X]).natDegree = 1 - 1 := natDegree_one
  have hred : ¬ Irreducible ((cyclotomic 3 ℤ).comp (X ^ 2)) := by
    intro hirr
    have hfactor : (cyclotomic 3 ℤ).comp (X ^ 2) = cyclotomic 6 ℤ * cyclotomic 3 ℤ := by
      simpa only [expand_eq_comp_X_pow] using
        cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (n := 3) (by norm_num) ℤ
    exact (hirr.isUnit_or_isUnit hfactor).elim hirr₆.not_isUnit hirr₃.not_isUnit
  have h := (l_eq_min_support_and_lt _ _ _ 1 1 h01 hirr₃ hrec hnc natDegree_cyclotomic_three
    hdecomp hfe hfo odd_one one_pos hred).2.2
  omega

end MathlibExtTest.ReciprocalZeroOneFirstOddExponent
