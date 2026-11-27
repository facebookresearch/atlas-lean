/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.AlignedForms

/-!
# Tests for translates, aligned forms and their composition

Knapp's example after Proposition 1.9: the aligned forms $2x^2 + 2xy + 3y^2$ and
$3x^2 + 2xy + 2y^2$ of discriminant $-20$, with $j = 1$, compose to the primitive form
$6x^2 + 2xy + y^2$ of discriminant $-20$. Also: the translate $(2, 5, 6)$ of $(2, 1, 3)$, Knapp's
remark after Lemma 1.11 with $l = 2$ and $(1, 2, 4)$, the alignment of $(2, 1, 3)$ and $(3, 1, 2)$,
the two cases where an integral multiplier does not give Knapp's aligned forms ($(2, 0, 2)$ with
$(1, 0, 4)$, and $(0, 1, 0)$ taken twice), and the existence statements on small forms.
-/

namespace BinaryQuadraticForm.AlignedFormsTest

-- Knapp, p. 25: `(2, 2, 3)` and `(3, 2, 2)` are aligned with `j = 1`, and compose to `(6, 2, 1)`.
example : Int.gcd (Int.gcd (2 * 3) 2 : ℤ) 1 = 1 ∧ discrim (2 * 3 : ℤ) 2 1 = -20 := by
  obtain ⟨hprim, hdisc, -, -⟩ := composition_of_aligned (a₁ := 2) (a₂ := 3) (b := 2) (c₁ := 3)
    (c₂ := 2) (j := 1) (by decide) (by decide) (by norm_num) (by norm_num)
  exact ⟨hprim, by rw [hdisc]; norm_num [discrim]⟩

-- The product of the values `2` at `(1, 0)` and `3` at `(1, 0)` is the value `6` of `(6, 2, 1)`.
example : (2 * 1 ^ 2 + 2 * 1 * 0 + 3 * 0 ^ 2 : ℤ) * (3 * 1 ^ 2 + 2 * 1 * 0 + 2 * 0 ^ 2) =
    2 * 3 * (1 * 1 - 1 * 0 * 0) ^ 2 +
      2 * (1 * 1 - 1 * 0 * 0) * (2 * 1 * 0 + 3 * 1 * 0 + 2 * 0 * 0) +
      1 * (2 * 1 * 0 + 3 * 1 * 0 + 2 * 0 * 0) ^ 2 :=
  (composition_of_aligned (a₁ := 2) (a₂ := 3) (b := 2) (c₁ := 3) (c₂ := 2) (j := 1)
    (by decide) (by decide) (by norm_num) (by norm_num)).2.2.1 1 0 1 0

-- The translate of `(2, 1, 3)`, of discriminant `-23`, with middle coefficient `5 ≡ 1 [ZMOD 4]`.
example : ProperlyEquivalent (2, 1, 3) (2, 5, 6) := by
  have h := (translate (a := 2) (b := 1) (c := 3) (b' := 5)
    (not_isSquare_of_neg (by norm_num [discrim])) (by decide)).2.2.2
  norm_num [discrim] at h
  exact h

example : ProperlyEquivalent (2, 1, 3) (2, 1 + 2 * 2 * 1, 2 * 1 ^ 2 + 1 * 1 + 3) :=
  properlyEquivalent_translate 2 1 3 1

-- Proper equivalence keeps positive definiteness: the translate has positive first coefficient.
example : (0 : ℤ) < 2 :=
  (properlyEquivalent_invariants.2.2.2 (properlyEquivalent_translate 2 1 3 1)
    (by norm_num [discrim])).mpr (by norm_num)

-- Knapp's remark after Lemma 1.11: `l = 2` and `(1, 2, 4)` give `(2, 2, 2)`, not primitive.
example : ProperlyEquivalent (2 * 1, 2, 4 / 2) (2 * 1, 2, 4 / 2) :=
  ProperlyEquivalent.mul_fst_div_snd (ProperlyEquivalent.refl (1, 2, 4)) (by decide)
    (by norm_num) (by norm_num)

example : Int.gcd (Int.gcd (2 * 1) 2 : ℤ) (4 / 2) = 2 := by decide

-- `x² + y²` takes the value `2` at the primitive vector `(1, 1)`.
example : ∃ b' c' : ℤ, ProperlyEquivalent (1, 0, 1) (2, b', c') ∧ discrim 2 b' c' = -4 := by
  obtain ⟨b', c', h, hd⟩ := exists_properlyEquivalent_fst_eq (1, 0, 1) (x₀ := 1) (y₀ := 1)
    (by decide)
  norm_num [discrim] at h hd ⊢
  exact ⟨b', c', h, by linarith⟩

-- Lemma 1.10 for `x² + y²` and `m = 10`.
example : ∃ x₀ y₀ : ℤ, Int.gcd x₀ y₀ = 1 ∧
    Int.gcd 10 (1 * x₀ ^ 2 + 0 * x₀ * y₀ + 1 * y₀ ^ 2) = 1 :=
  exists_gcd_eq_one_value (by decide) (by norm_num)

-- `(2, 1, 3)` and `(3, 1, 2)`, of discriminant `-23`, are aligned with `j = 1`.
example : ∃ j : ℤ, (3 : ℤ) = j * 3 ∧ (2 : ℤ) = j * 2 :=
  (exists_eq_mul_of_gcd_eq_one (a₁ := 2) (a₂ := 3) (b := 1) (c₁ := 3) (c₂ := 2)
    (not_isSquare_of_neg (by norm_num [discrim])) (by norm_num [discrim]) (by decide)).2.2

-- Without primitivity an integral multiplier does not give aligned forms: `(2, 0, 2)` and
-- `(1, 0, 4)`, of discriminant `-16`, have `j = 2`, but `(2, 0, 2)` has content `2`.
example : ∃ j : ℤ, (2 : ℤ) = j * 1 ∧ (4 : ℤ) = j * 2 :=
  (exists_eq_mul_of_gcd_eq_one (a₁ := 2) (a₂ := 1) (b := 0) (c₁ := 2) (c₂ := 4)
    (not_isSquare_of_neg (by norm_num [discrim])) (by norm_num [discrim]) (by decide)).2.2

example : Int.gcd (Int.gcd 2 0 : ℤ) 2 = 2 := by decide

-- With zero first coefficients the multiplier is not determined: `(0, 1, 0)` taken twice meets
-- the hypotheses of `composition_of_aligned` for every `j`.
example (j : ℤ) : Int.gcd (Int.gcd (0 * 0) 1 : ℤ) j = 1 :=
  (composition_of_aligned (a₁ := 0) (a₂ := 0) (b := 1) (c₁ := 0) (c₂ := 0) (j := j)
    (by decide) (by decide) (by ring) (by ring)).1

-- Theorem 1.12(a) for the classes of `2x² + xy + 3y²` and `2x² - xy + 3y²`, with `m = 6`.
example : ∃ a₁ a₂ b c₁ c₂ j : ℤ, ProperlyEquivalent (2, 1, 3) (a₁, b, c₁) ∧
    ProperlyEquivalent (2, -1, 3) (a₂, b, c₂) ∧ c₁ = j * a₂ ∧ c₂ = j * a₁ ∧
    Int.gcd a₁ a₂ = 1 ∧ Int.gcd a₁ 6 = 1 ∧ Int.gcd a₂ 6 = 1 :=
  exists_aligned (f₁ := (2, 1, 3)) (f₂ := (2, -1, 3)) (by decide) (by decide)
    (not_isSquare_of_neg (by norm_num [discrim])) (by norm_num [discrim]) (by norm_num)

end BinaryQuadraticForm.AlignedFormsTest
