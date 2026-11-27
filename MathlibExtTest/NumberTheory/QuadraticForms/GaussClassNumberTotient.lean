/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumberTotient
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the totient lower bounds for Gauss class numbers

The bounds of `MetaMathlibExt.gaussClassNumber_mul_totient_le` at small discriminants, with the
class numbers computed by `decide`. At $D = -3$ and $f = 7$ the second bound is an equality:
$\varphi(7) = 6 = 3\, h(-147)$.

The reduction theory of the module on concrete forms: the Gauss-reduced form properly equivalent
to $2x^2 + 6xy + 5y^2$ is $x^2 + y^2$, and the reduced forms $2x^2 \pm xy + 3y^2$ are not properly
equivalent.
-/

namespace MetaMathlibExt.GaussClassNumberTotientTest

open ImaginaryQuadraticDiscriminant

theorem fundamental_neg_seven : IsFundamentalImaginaryQuadraticDiscriminant (-7) :=
  ⟨by norm_num, Or.inl ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree, by decide⟩⟩

theorem fundamental_neg_three : IsFundamentalImaginaryQuadraticDiscriminant (-3) :=
  ⟨by norm_num, Or.inl ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree, by decide⟩⟩

theorem fundamental_neg_four : IsFundamentalImaginaryQuadraticDiscriminant (-4) :=
  ⟨by norm_num, Or.inr ⟨-1, by norm_num, by simp, by decide⟩⟩

-- `h(-7) φ(3) ≤ h(-63)`, from the first bound.
example : gaussClassNumber (-7) * Nat.totient 3 ≤ gaussClassNumber ((3 : ℕ) ^ 2 * (-7)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_seven (by norm_num)).1 (by norm_num)
    (by norm_num)

-- The computed values: `h(-7) = 1`, `φ(3) = 2` and `h(-63) = 4`.
example : gaussClassNumber (-7) = 1 ∧ Nat.totient 3 = 2 ∧ gaussClassNumber (-63) = 4 := by
  refine ⟨by decide +kernel, by decide, by decide +kernel⟩

-- `φ(7) ≤ 3 h(-147)`, from the second bound; here `h(-147) = 2`, so equality holds.
example : Nat.totient 7 ≤ 3 * gaussClassNumber ((7 : ℕ) ^ 2 * (-3)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_three (by norm_num)).2 (Or.inl rfl)

example : Nat.totient 7 = 6 ∧ gaussClassNumber (-147) = 2 := by
  refine ⟨by decide, by decide +kernel⟩

-- `φ(5) ≤ 3 h(-100)` at `D = -4`; here `h(-100) = 2`.
example : Nat.totient 5 ≤ 3 * gaussClassNumber ((5 : ℕ) ^ 2 * (-4)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_four (by norm_num)).2 (Or.inr rfl)

example : gaussClassNumber (-100) = 2 := by decide +kernel

-- At `f = 1` the first bound reads `h(D) ≤ h(D)`.
example : gaussClassNumber (-7) * Nat.totient 1 ≤ gaussClassNumber ((1 : ℕ) ^ 2 * (-7)) :=
  (gaussClassNumber_mul_totient_le fundamental_neg_seven le_rfl).1 (by norm_num) (by norm_num)

section Reduction

open GaussClassNumberTotient BinaryQuadraticForm

theorem isGaussReduced_one_zero_one : IsGaussReduced 1 0 1 :=
  IsGaussReduced.mk (by norm_num) (by norm_num [discrim]) (by norm_num) le_rfl (by norm_num)

-- The substitution `x ↦ x + y`, `y ↦ x + 2y`, of determinant `1`, takes `x² + y²` to
-- `2x² + 6xy + 5y²`.
theorem properlyEquivalent_one_zero_one_two_six_five : ProperlyEquivalent (1, 0, 1) (2, 6, 5) :=
  ⟨⟨!![1, 1; 1, 2], by rw [Matrix.det_fin_two_of]; norm_num⟩, rfl⟩

-- `exists_reduced` on `2x² + 6xy + 5y²`, of discriminant `-4`, gives a reduced form `G` properly
-- equivalent to it. By the substitution above and transitivity, the reduced form `x² + y²` is
-- properly equivalent to `G` too, so `eq_of_equiv_of_reduced` gives `G = x² + y²`.
example :
    ∃ G, ProperlyEquivalent (2, 6, 5) G ∧ IsGaussReduced G.1 G.2.1 G.2.2 ∧ G = (1, 0, 1) := by
  obtain ⟨G, hFG, hred⟩ := exists_reduced (2, 6, 5) (by norm_num) (by norm_num [discrim])
  refine ⟨G, hFG, hred, ?_⟩
  exact (eq_of_equiv_of_reduced isGaussReduced_one_zero_one hred
    (properlyEquivalent_one_zero_one_two_six_five.trans hFG)).symm

-- `2x² + xy + 3y²` and `2x² - xy + 3y²` are distinct reduced forms of discriminant `-23`, so they
-- are not properly equivalent, though `x ↦ -x` takes one to the other.
example : ¬ ProperlyEquivalent (2, 1, 3) (2, -1, 3) := fun h =>
  absurd (eq_of_equiv_of_reduced
    (IsGaussReduced.mk (by norm_num) (by norm_num [discrim]) (by norm_num) (by norm_num)
      (by norm_num))
    (IsGaussReduced.mk (by norm_num) (by norm_num [discrim]) (by norm_num) (by norm_num)
      (by norm_num)) h) (by decide)

end Reduction

end MetaMathlibExt.GaussClassNumberTotientTest
