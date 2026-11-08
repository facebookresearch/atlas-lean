/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.Reverse

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.LehmerConstant

/-!
# Lehmer's Mahler measure constant

For an integer polynomial `f`, its Mahler measure is
`M(f) = |a| * ∏ᵢ max (1, |αᵢ|)`, where `a` is the leading coefficient and
the `αᵢ` are the complex roots of `f` counted with multiplicity. This is
`Polynomial.mapMahlerMeasure (Int.castRingHom ℂ)` in Mathlib, whose root
product formula is `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`.

Lehmer's constant (catalogue constant C40a) is the infimum of the Mahler
measures strictly larger than `1` among integer polynomials:
`L = inf {M(f) | f ∈ ℤ[X], 1 < M(f)}`. Lehmer's 1933 question asks whether
Mahler measures accumulate at `1`, equivalently whether `L = 1`; this file
proves that equivalence together with the elementary bounds `1 ≤ L ≤ 2`.
The sharp catalogue upper bound from Lehmer's example polynomial and
Smyth's nonreciprocal lower bound are registered as proof requests in the
wanted file.

Source: Optimization Problems, constants/40a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`d89b66d6b78a2de211675ee1e2deb67f427fc66a3d051adad8a740a28397e3e6`.
-/

/-- The Mahler measure of an integer polynomial: the Mahler measure of its
image in `ℂ[X]`. -/
noncomputable def intMahlerMeasure (f : Polynomial ℤ) : ℝ :=
  f.mapMahlerMeasure (Int.castRingHom ℂ)

theorem intMahlerMeasure_nonneg (f : Polynomial ℤ) :
    0 ≤ intMahlerMeasure f :=
  Polynomial.mahlerMeasure_nonneg _

/-- A nonzero integer polynomial has Mahler measure at least `1`: its
leading coefficient is a nonzero integer, and every root factor
`max (1, |α|)` is at least `1`. -/
theorem one_le_intMahlerMeasure {f : Polynomial ℤ} (hf : f ≠ 0) :
    1 ≤ intMahlerMeasure f := by
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
  calc
    (1 : ℝ) ≤ ‖f.leadingCoeff‖ := by
      rw [Int.norm_eq_abs]
      exact_mod_cast Int.one_le_abs hlc
    _ ≤ intMahlerMeasure f :=
      Polynomial.leadingCoeff_le_mapMahlerMeasure _ _ Complex.isometry_intCast

theorem intMahlerMeasure_mul (f g : Polynomial ℤ) :
    intMahlerMeasure (f * g) = intMahlerMeasure f * intMahlerMeasure g := by
  simp only [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_mul,
    Polynomial.mahlerMeasure_mul]

theorem intMahlerMeasure_C (a : ℤ) :
    intMahlerMeasure (C a) = ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_C,
    Polynomial.mahlerMeasure_const]
  simp

/-- Mahler measure of a linear factor `X - a` over the integers. -/
theorem intMahlerMeasure_X_sub_C (a : ℤ) :
    intMahlerMeasure (X - C a) = max 1 ‖(a : ℝ)‖ := by
  rw [intMahlerMeasure, Polynomial.mapMahlerMeasure, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.mahlerMeasure_X_sub_C]
  simp

theorem intMahlerMeasure_X : intMahlerMeasure (X : Polynomial ℤ) = 1 := by
  have h : (X : Polynomial ℤ) = X - C (0 : ℤ) := by simp
  rw [h, intMahlerMeasure_X_sub_C]
  simp

/-- The polynomial `X - 1` has Mahler measure `1`, on the boundary excluded
from Lehmer's infimum. -/
theorem intMahlerMeasure_X_sub_one :
    intMahlerMeasure (X - C (1 : ℤ)) = 1 := by
  rw [intMahlerMeasure_X_sub_C]
  simp

/-- The polynomial `X - 2` has Mahler measure `2`, a concrete member of
Lehmer's infimum set. -/
theorem intMahlerMeasure_X_sub_two :
    intMahlerMeasure (X - C (2 : ℤ)) = 2 := by
  rw [intMahlerMeasure_X_sub_C]
  norm_num

/-- The set of Mahler measures of integer polynomials that are strictly
larger than `1`. -/
def mahlerMeasuresAboveOne : Set ℝ :=
  {y | ∃ f : Polynomial ℤ, 1 < intMahlerMeasure f ∧ y = intMahlerMeasure f}

/-- **Lehmer's constant** `C₄₀ₐ`: the infimum of the Mahler measures
strictly larger than `1` among integer polynomials. -/
noncomputable def lehmerConstant : ℝ :=
  sInf mahlerMeasuresAboveOne

theorem mahlerMeasuresAboveOne_nonempty : mahlerMeasuresAboveOne.Nonempty :=
  ⟨2, X - C (2 : ℤ), by rw [intMahlerMeasure_X_sub_two]; norm_num,
    intMahlerMeasure_X_sub_two.symm⟩

theorem mahlerMeasuresAboveOne_bddBelow : BddBelow mahlerMeasuresAboveOne :=
  ⟨1, by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf⟩

/-- Every Mahler measure in the defining set bounds Lehmer's constant from
above. -/
theorem lehmerConstant_le_intMahlerMeasure {f : Polynomial ℤ}
    (hf : 1 < intMahlerMeasure f) : lehmerConstant ≤ intMahlerMeasure f :=
  csInf_le mahlerMeasuresAboveOne_bddBelow ⟨f, hf, rfl⟩

/-- Catalogue lower bound: `1 ≤ C₄₀ₐ`. -/
theorem one_le_lehmerConstant : 1 ≤ lehmerConstant :=
  le_csInf mahlerMeasuresAboveOne_nonempty (by
    rintro y ⟨f, hf, rfl⟩
    exact le_of_lt hf)

/-- Elementary upper bound from the witness `X - 2`: `C₄₀ₐ ≤ 2`. -/
theorem lehmerConstant_le_two : lehmerConstant ≤ 2 := by
  rw [← intMahlerMeasure_X_sub_two]
  exact lehmerConstant_le_intMahlerMeasure (by
    rw [intMahlerMeasure_X_sub_two]; norm_num)

/-- Lehmer's 1933 question: there are integer polynomials with Mahler
measure arbitrarily close to `1` from above. -/
def LehmerQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : Polynomial ℤ,
    1 < intMahlerMeasure f ∧ intMahlerMeasure f < 1 + ε

/-- Lehmer's question is equivalent to Lehmer's constant being `1`. -/
theorem lehmerConstant_eq_one_iff : lehmerConstant = 1 ↔ LehmerQuestion := by
  constructor
  · intro hL ε hε
    obtain ⟨y, ⟨f, hf, rfl⟩, hy⟩ := exists_lt_of_csInf_lt
      mahlerMeasuresAboveOne_nonempty (show lehmerConstant < 1 + ε by linarith)
    exact ⟨f, hf, hy⟩
  · intro hQ
    apply le_antisymm _ one_le_lehmerConstant
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf1, hf2⟩ := hQ ε hε
    linarith [lehmerConstant_le_intMahlerMeasure hf1]

/-- Lehmer's 1933 example polynomial
`X^10 + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1`, whose Mahler measure
`1.176280...` is still the smallest known value larger than `1`. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- Smyth's polynomial `X^3 - X - 1`, whose Mahler measure (the plastic
number `1.324717...`) bounds all nonreciprocal integer polynomials from
below. -/
noncomputable def smythPolynomial : Polynomial ℤ :=
  X ^ 3 - X - 1

/-- An integer polynomial is reciprocal when reversing its coefficients
gives the polynomial or its negation: `f.reverse = ±f`, equivalently
`X ^ deg f * f (1 / X) = ±f`. -/
def IsReciprocal (f : Polynomial ℤ) : Prop :=
  f.reverse = f ∨ f.reverse = -f

theorem isReciprocal_one : IsReciprocal (1 : Polynomial ℤ) := by
  left
  simp [Polynomial.reverse]

end MathlibExt.NumberTheory.LehmerConstant
