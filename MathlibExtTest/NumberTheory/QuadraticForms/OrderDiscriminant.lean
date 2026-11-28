/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.OrderDiscriminant

open Complex PeriodPair

open scoped ComplexConjugate

/-- `ℤ + ℤi` and `ℤ + ℤ(1 - i)` are the same lattice. -/
example : ((ofTau I (by simp)).lattice : Set ℂ) = (ofTau (1 - I) (by simp)).lattice :=
  (lattice_ofTau_eq_iff _ _).mpr ⟨1, Or.inr (by push_cast; ring)⟩

/-- `-4` is an imaginary quadratic discriminant, and its order has discriminant `-4`. -/
example : ∃ _hω : ((((-4 : ℤ) : ℂ) + I * (Real.sqrt |((-4 : ℤ) : ℝ)| : ℂ)) / 2).im ≠ 0,
    ((((-4 : ℤ) : ℂ) + I * (Real.sqrt |((-4 : ℤ) : ℝ)| : ℂ)) / 2 -
      conj ((((-4 : ℤ) : ℂ) + I * (Real.sqrt |((-4 : ℤ) : ℝ)| : ℂ)) / 2)) ^ 2 = ((-4 : ℤ) : ℂ) := by
  obtain ⟨hω, -, hdisc, -⟩ := order_of_discriminant (D := -4) ⟨by norm_num, by norm_num⟩
  exact ⟨hω, hdisc⟩

/-- The discriminant of `ℤ + ℤi` is the integer `-4`. -/
example : ∃ D : ℤ, D < 0 ∧ (I - conj I) ^ 2 = D :=
  exists_sq_sub_conj_eq_intCast (ω := I) (by simp)
    (mem_lattice_ofTau.mpr ⟨-1, 0, by simp⟩)
