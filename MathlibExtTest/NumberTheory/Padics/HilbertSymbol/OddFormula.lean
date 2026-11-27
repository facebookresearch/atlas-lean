/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.OddFormula

/-!
# Tests for the formula for the $p$-adic Hilbert symbol at an odd prime
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbolOddFormulaTest

/-- The formula with the source's binders. -/
example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b : ℚ_[p]ˣ) (α β : ℤ) (u v : ℤ_[p]ˣ)
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]))
    (hb : (b : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p])) :
    padicHilbertSymbol p a b =
      (-1) ^ (α * β * ((p - 1) / 2 : ℕ)).natAbs *
        legendreSym p (PadicInt.toZMod (u : ℤ_[p])).val ^ β.natAbs *
        legendreSym p (PadicInt.toZMod (v : ℤ_[p])).val ^ α.natAbs :=
  padicHilbertSymbol.eq_formula_of_ne_two hp2 a b α β u v ha hb

/-- The general field lemmas. -/
example {F : Type} [Field F] (a b c : Fˣ) :
    hilbertSymbol F (a * c ^ 2) b = hilbertSymbol F b a := by
  rw [hilbertSymbol.mul_sq_left, hilbertSymbol.comm]

example {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (a : Fˣ) : hilbertSymbol F a (-a) = 1 := by
  rw [hilbertSymbol.eq_one_iff_exists_ternary_eq_zero h2]
  exact ⟨0, 1, 1, fun h => one_ne_zero h.2.1, by simp⟩

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- At `p = 3` the sign term is `-1`: $(3, 3)_3 = (-1)^{(3 - 1)/2} = -1$. -/
example : padicHilbertSymbol 3 (Units.mk0 (3 : ℚ_[3]) (by norm_num))
    (Units.mk0 (3 : ℚ_[3]) (by norm_num)) = -1 := by
  rw [padicHilbertSymbol.eq_formula_of_ne_two (by decide) _ _ 1 1 1 1 (by simp) (by simp)]
  simp [ZMod.val_one]

/-- At `p = 5` the sign term is `1`: $(5, 5)_5 = (-1)^{(5 - 1)/2} = 1$. -/
example : padicHilbertSymbol 5 (Units.mk0 (5 : ℚ_[5]) (by norm_num))
    (Units.mk0 (5 : ℚ_[5]) (by norm_num)) = 1 := by
  rw [padicHilbertSymbol.eq_formula_of_ne_two (by decide) _ _ 1 1 1 1 (by simp) (by simp)]
  simp [ZMod.val_one]

/-- Negative valuations are allowed: with $\alpha = -2$ and $\beta = -1$ the formula gives
$(3^{-2}, 3^{-1})_3 = 1$, as $3^{-2}$ is a square. -/
example : padicHilbertSymbol 3 (Units.mk0 ((3 : ℚ_[3]) ^ (-2 : ℤ)) (by norm_num))
    (Units.mk0 ((3 : ℚ_[3]) ^ (-1 : ℤ)) (by norm_num)) = 1 := by
  rw [padicHilbertSymbol.eq_formula_of_ne_two (by decide) _ _ (-2) (-1) 1 1 (by simp) (by simp)]
  simp [ZMod.val_one]

/-- A unit of `ℤ_[3]` whose residue is a square is a square. -/
example : IsSquare (4 : ℤ_[3]) :=
  PadicInt.isSquare_of_isSquare_toZMod (p := 3) (by decide) (by rw [map_ofNat]; decide)
    ⟨2, by rw [map_ofNat]; decide⟩

end HilbertSymbolOddFormulaTest
