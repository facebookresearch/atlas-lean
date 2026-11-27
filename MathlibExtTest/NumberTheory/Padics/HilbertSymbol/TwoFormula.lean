/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.TwoFormula

/-!
# Tests for the formula for the $2$-adic Hilbert symbol
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbolTwoFormulaTest

/-- The formula with the source's binders. -/
example (a b : ℚ_[2]ˣ) (α β : ℤ) (u v : ℤ_[2]ˣ)
    (ha : (a : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]))
    (hb : (b : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2])) :
    padicHilbertSymbol 2 a b =
      (-1) ^ (((PadicInt.toZModPow 3 (u : ℤ_[2])).val - 1) / 2 *
            (((PadicInt.toZModPow 3 (v : ℤ_[2])).val - 1) / 2) +
          α.natAbs * (((PadicInt.toZModPow 3 (v : ℤ_[2])).val ^ 2 - 1) / 8) +
          β.natAbs * (((PadicInt.toZModPow 3 (u : ℤ_[2])).val ^ 2 - 1) / 8)) :=
  padicHilbertSymbol.eq_formula_two a b α β u v ha hb

/-- $(-1, -1)_2 = (-1)^{\varepsilon(-1)^2} = -1$. -/
example : padicHilbertSymbol 2 (-1) (-1) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 0 0 (-1) (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- $(2, -1)_2 = (-1)^{\omega(-1)} = 1$. -/
example : padicHilbertSymbol 2 (Units.mk0 (2 : ℚ_[2]) (by norm_num)) (-1) = 1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 1 0 1 (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- $(-2, -2)_2 = (-1)^{\varepsilon(-1)^2 + 2\omega(-1)} = -1$. -/
example : padicHilbertSymbol 2 (Units.mk0 (-2 : ℚ_[2]) (by norm_num))
    (Units.mk0 (-2 : ℚ_[2]) (by norm_num)) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 1 1 (-1) (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- Negative valuations are allowed: with $\alpha = -1$ the formula gives
$(-2^{-1}, -1)_2 = -1$. -/
example : padicHilbertSymbol 2 (Units.mk0 (-(2 : ℚ_[2]) ^ (-1 : ℤ)) (by norm_num)) (-1) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ (-1) 0 (-1) (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- An element of `ℤ_[2]` congruent to `1` modulo `8` is a square. -/
example : IsSquare (-7 : ℤ_[2]) :=
  PadicInt.isSquare_of_toZModPow_three_eq_one (by rw [map_neg, map_ofNat]; decide)

/-- The unit `-1` of `ℤ_[2]` is not a square. -/
example : ¬IsSquare ((-1 : ℤ_[2]ˣ) : ℤ_[2]) := by
  rw [PadicInt.isSquare_unit_iff_toZModPow_three_eq_one]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

end HilbertSymbolTwoFormulaTest
