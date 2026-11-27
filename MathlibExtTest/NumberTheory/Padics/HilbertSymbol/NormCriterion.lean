/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.NormCriterion
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.FieldTheory.KummerPolynomial

/-!
# Tests for the norm criterion and the first properties of the Hilbert symbol
-/

set_option autoImplicit false

@[expose] public section

open IntermediateField Polynomial

namespace HilbertSymbolNormCriterionTest

/-- The norm criterion with the source's binders, for a square root `β` of `b` in an extension. -/
example {F L : Type*} [Field F] [Field L] [Algebra F L] (h2 : (2 : F) ≠ 0) (a b : Fˣ) (β : L)
    (hβ : β ^ 2 = algebraMap F L b) :
    hilbertSymbol F a b = 1 ↔ ∃ ξ : (F⟮β⟯)ˣ, Algebra.norm F (ξ : F⟮β⟯) = a :=
  hilbertSymbol.eq_one_iff_exists_norm_eq h2 a b hβ

/-- The norm criterion in the explicit form `a = z ^ 2 - b y ^ 2`. -/
example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b : Fˣ) :
    hilbertSymbol F a b = 1 ↔ ∃ z y : F, (a : F) = z ^ 2 - b * y ^ 2 :=
  hilbertSymbol.eq_one_iff_exists_eq_sq_sub_mul_sq h2 a b

/-- The norm criterion for `ℂ = ℝ(√-1)`, with `β = i`. -/
example (a : ℝˣ) :
    hilbertSymbol ℝ a (-1) = 1 ↔ ∃ ξ : (ℝ⟮Complex.I⟯)ˣ, Algebra.norm ℝ (ξ : ℝ⟮Complex.I⟯) = a :=
  hilbertSymbol.eq_one_iff_exists_norm_eq two_ne_zero a (-1) (by
    rw [Complex.I_sq, Units.val_neg, Units.val_one, map_neg, map_one])

/-- `X ^ 2 - b` is irreducible when `b` is not a square. -/
example {F : Type*} [Field F] (b : F) (hb : ¬IsSquare b) : Irreducible (X ^ 2 - C b) :=
  irreducible_X_pow_sub_C_of_prime Nat.prime_two fun c hc => hb ⟨c, by rw [← hc, sq]⟩

/-- The first properties with the source's binders. -/
example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a a' b c : Fˣ) :
    (hilbertSymbol F a b = hilbertSymbol F b a ∧ hilbertSymbol F a (c ^ 2) = 1) ∧
      (hilbertSymbol F a (-a) = 1 ∧
        ∀ ha : 1 - (a : F) ≠ 0, hilbertSymbol F a (Units.mk0 (1 - (a : F)) ha) = 1) ∧
      (hilbertSymbol F a b = 1 → hilbertSymbol F (a * a') b = hilbertSymbol F a' b) ∧
      (hilbertSymbol F a b = hilbertSymbol F a (-(a * b)) ∧
        ∀ ha : 1 - (a : F) ≠ 0,
          hilbertSymbol F a b = hilbertSymbol F a (Units.mk0 (1 - (a : F)) ha * b)) :=
  hilbertSymbol.first_properties h2 a a' b c

/-- The individual parts, and invariance under squares in the second argument. -/
example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b c : Fˣ) (ha : 1 - (a : F) ≠ 0) :
    hilbertSymbol F a (c ^ 2) = 1 ∧ hilbertSymbol F a (-a) = 1 ∧
      hilbertSymbol F a (Units.mk0 (1 - (a : F)) ha) = 1 ∧
      hilbertSymbol F a (b * c ^ 2) = hilbertSymbol F a b ∧
      hilbertSymbol F a b = hilbertSymbol F a (-(a * b)) ∧
      hilbertSymbol F a b = hilbertSymbol F a (Units.mk0 (1 - (a : F)) ha * b) :=
  ⟨hilbertSymbol.sq_right a c, hilbertSymbol.self_neg h2 a, hilbertSymbol.self_one_sub a ha,
    hilbertSymbol.mul_sq_right a b c, hilbertSymbol.eq_neg_mul_right h2 a b,
    hilbertSymbol.eq_one_sub_mul_right h2 a b ha⟩

/-- Over `ℝ`, the norm form `z ^ 2 + y ^ 2` of `ℝ(√-1)` does not take the value `-1`. -/
example : ¬∃ z y : ℝ, (-1 : ℝ) = z ^ 2 - (-1) * y ^ 2 := by
  intro ⟨z, y, h⟩
  nlinarith [sq_nonneg z, sq_nonneg y]

/-- Over `ℝ`, the criterion recovers `(-1, -1) = -1` from the norm form. -/
example : hilbertSymbol ℝ (-1) (-1) = -1 := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rcases hilbertSymbol.eq_one_or_neg_one (F := ℝ) (-1) (-1) with h | h
  · obtain ⟨z, y, hzy⟩ := (hilbertSymbol.eq_one_iff_exists_eq_sq_sub_mul_sq h2 _ _).1 h
    simp only [Units.val_neg, Units.val_one] at hzy
    nlinarith [sq_nonneg z, sq_nonneg y]
  · exact h

/-- A square second argument: `(a, 4) = 1` over `ℚ`. -/
example (a : ℚˣ) : hilbertSymbol ℚ a (Units.mk0 4 (by norm_num)) = 1 :=
  hilbertSymbol.eq_one_of_isSquare_right ⟨2, by norm_num⟩

/-- `(2, -1) = 1` over `ℚ`, from `(2, 1 - 2) = 1`. -/
example : hilbertSymbol ℚ (Units.mk0 2 (by norm_num)) (-1) = 1 := by
  have h := hilbertSymbol.self_one_sub (F := ℚ) (Units.mk0 2 (by norm_num)) (by norm_num)
  convert h using 2
  ext
  simp only [Units.val_neg, Units.val_one, Units.val_mk0]
  norm_num

end HilbertSymbolNormCriterionTest
