/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Bilinear

/-!
# Tests for the bilinearity and nondegeneracy of the $p$-adic Hilbert symbol
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbolBilinearTest

/-- Multiplicativity in the first argument, with the source's binders. -/
example (p : ℕ) [Fact p.Prime] (a a' b : ℚ_[p]ˣ) :
    padicHilbertSymbol p (a * a') b = padicHilbertSymbol p a b * padicHilbertSymbol p a' b :=
  padicHilbertSymbol.mul_left a a' b

/-- Multiplicativity in the second argument. -/
example (p : ℕ) [Fact p.Prime] (a b b' : ℚ_[p]ˣ) :
    padicHilbertSymbol p a (b * b') = padicHilbertSymbol p a b * padicHilbertSymbol p a b' :=
  padicHilbertSymbol.mul_right a b b'

/-- Symmetry, for the $p$-adic symbol. -/
example (p : ℕ) [Fact p.Prime] (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = padicHilbertSymbol p b a :=
  hilbertSymbol.comm a b

/-- Nondegeneracy, as in the source. -/
example (p : ℕ) [Fact p.Prime] (b : ℚ_[p]ˣ) (h : ∀ a : ℚ_[p]ˣ, padicHilbertSymbol p a b = 1) :
    IsSquare b :=
  (padicHilbertSymbol.forall_eq_one_iff_isSquare b).1 h

/-- The symbol is trivial against a square. -/
example (p : ℕ) [Fact p.Prime] (a c : ℚ_[p]ˣ) : padicHilbertSymbol p a (c * c) = 1 :=
  (padicHilbertSymbol.forall_eq_one_iff_isSquare (c * c)).2 ⟨c, rfl⟩ a

/-- $(-1, -1)_2 = -1$. -/
theorem neg_one_neg_one_two : padicHilbertSymbol 2 (-1) (-1) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 0 0 (-1) (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- $(2, -1)_2 = 1$. -/
theorem two_neg_one_two : padicHilbertSymbol 2 (Units.mk0 (2 : ℚ_[2]) (by norm_num)) (-1) = 1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 1 0 1 (-1) (by simp) (by simp)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- Bilinearity evaluates $(-2, -1)_2 = (2, -1)_2 \, (-1, -1)_2 = -1$. -/
example : padicHilbertSymbol 2 (Units.mk0 (2 : ℚ_[2]) (by norm_num) * -1) (-1) = -1 := by
  rw [padicHilbertSymbol.mul_left, two_neg_one_two, neg_one_neg_one_two]
  norm_num

/-- Nondegeneracy detects that $-1$ is not a square in $\mathbb{Q}_2$. -/
example : ¬IsSquare (-1 : ℚ_[2]ˣ) := by
  rw [← padicHilbertSymbol.forall_eq_one_iff_isSquare]
  intro h
  have := h (-1)
  rw [neg_one_neg_one_two] at this
  norm_num at this

/-- Bilinearity gives $(9, 3)_3 = (3, 3)_3^2 = 1$. -/
example : padicHilbertSymbol 3 (Units.mk0 (3 : ℚ_[3]) (by norm_num) *
    Units.mk0 (3 : ℚ_[3]) (by norm_num)) (Units.mk0 (3 : ℚ_[3]) (by norm_num)) = 1 := by
  rw [padicHilbertSymbol.mul_left]
  rcases padicHilbertSymbol.eq_one_or_neg_one (p := 3) (Units.mk0 (3 : ℚ_[3]) (by norm_num))
    (Units.mk0 (3 : ℚ_[3]) (by norm_num)) with h | h <;> rw [h] <;> norm_num

end HilbertSymbolBilinearTest
