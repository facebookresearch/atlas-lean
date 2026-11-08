/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.AsymptoticDobrowolski

@[expose] public section

namespace AsymptoticDobrowolskiTest

/-- A nonintegral algebraic number exercises denominator clearing, primitivity, sign and root. -/
theorem half_positive_primitive_root :
    let x : ℂ := algebraMap ℚ ℂ (1 / 2)
    IsAlgebraic ℚ x ∧ x ≠ 0 ∧
      (NumberField.positivePrimitiveIntMinpoly x).IsPrimitive ∧
      0 < (NumberField.positivePrimitiveIntMinpoly x).leadingCoeff ∧
      (NumberField.positivePrimitiveIntMinpoly x).natDegree = 1 ∧
      Polynomial.eval₂ (Int.castRingHom ℂ) x
        (NumberField.positivePrimitiveIntMinpoly x) = 0 := by
  dsimp only
  have hx : IsAlgebraic ℚ (algebraMap ℚ ℂ (1 / 2)) :=
    isAlgebraic_algebraMap (1 / 2 : ℚ)
  refine ⟨hx, by norm_num, NumberField.positivePrimitiveIntMinpoly_isPrimitive _,
    NumberField.positivePrimitiveIntMinpoly_leadingCoeff_pos _, ?_,
    NumberField.positivePrimitiveIntMinpoly_eval₂_at _ hx⟩
  rw [NumberField.positivePrimitiveIntMinpoly_natDegree_eq, minpoly.eq_X_sub_C]
  simp

/-- An actual integral input supplies a populated positive primitive minimal-polynomial witness. -/
theorem two_has_positive_primitive_root :
    ∃ p : Polynomial ℤ,
      p = NumberField.positivePrimitiveIntMinpoly (algebraMap ℚ ℂ 2) ∧ p.IsPrimitive ∧ p ≠ 0 ∧
        0 < p.leadingCoeff ∧ p.natDegree = 1 ∧
        Polynomial.eval₂ (Int.castRingHom ℂ) (algebraMap ℚ ℂ 2) p = 0 := by
  refine ⟨NumberField.positivePrimitiveIntMinpoly (algebraMap ℚ ℂ 2), rfl,
    NumberField.positivePrimitiveIntMinpoly_isPrimitive _,
    NumberField.positivePrimitiveIntMinpoly_ne_zero _,
    NumberField.positivePrimitiveIntMinpoly_leadingCoeff_pos _, ?_,
    NumberField.positivePrimitiveIntMinpoly_eval₂_at _ (isAlgebraic_algebraMap (2 : ℚ))⟩
  rw [NumberField.positivePrimitiveIntMinpoly_natDegree_eq, minpoly.eq_X_sub_C]
  simp

/-- Zero has degree one, but is excluded by the source's nonzero hypothesis. -/
theorem zero_degree_one : (minpoly ℚ (0 : ℂ)).natDegree = 1 := by
  simp

/-- One is a root of unity and cannot enter the source's coefficient domain. -/
theorem one_isOfFinOrder : IsOfFinOrder (1 : ℂ) := IsOfFinOrder.one

/-- The totalized scale at one is zero; operative estimates impose degrees at least three. -/
theorem dobrowolskiScale_one :
    MathlibExt.NumberTheory.AsymptoticDobrowolski.dobrowolskiScale 1 = 0 := by
  simp [MathlibExt.NumberTheory.AsymptoticDobrowolski.dobrowolskiScale]

/-- The nonintegral input uses the canonical height, and degree one removes its denominator. -/
theorem half_height_eq_logMahlerMeasure :
    NumberField.absLogHeight₁ (algebraMap ℚ ℂ (1 / 2)) =
      Real.log (NumberField.algebraicMahlerMeasure (algebraMap ℚ ℂ (1 / 2))) := by
  rw [NumberField.absLogHeight₁_eq_log_algebraicMahlerMeasure _
    (isAlgebraic_algebraMap (1 / 2 : ℚ)), minpoly.eq_X_sub_C]
  simp

open MathlibExt.NumberTheory.AsymptoticDobrowolski

/-- The canonical model gives an actual uniform strict inequality at coefficient zero.
This does not assert any of the five unproved literature bounds. -/
theorem zero_uniform_strict_bound :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, 3 ≤ D ∧
      ∀ α : ℂ, IsAlgebraic ℚ α → α ≠ 0 → ¬IsOfFinOrder α →
        D ≤ (minpoly ℚ α).natDegree →
          1 + (0 - ε) * dobrowolskiScale (minpoly ℚ α).natDegree <
            NumberField.algebraicMahlerMeasure α :=
  isAsymptoticDobrowolskiCoefficient_iff_strict.mp zero_isAsymptoticDobrowolskiCoefficient

end AsymptoticDobrowolskiTest
