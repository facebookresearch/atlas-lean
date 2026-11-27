/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.ProductFormula

/-!
# Tests for Hilbert's product formula over $\mathbb{Q}$
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbolProductFormulaTest

/-- The product formula, with the source's binders. -/
example (a b : ℚˣ) :
    {p : Nat.Primes |
        haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
        padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom a)
          (Units.map (Rat.castHom ℚ_[p]).toMonoidHom b) ≠ 1}.Finite ∧
      realHilbertSymbol (Units.map (Rat.castHom ℝ).toMonoidHom a)
          (Units.map (Rat.castHom ℝ).toMonoidHom b) *
        ∏ᶠ p : Nat.Primes,
          (haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
          padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom a)
            (Units.map (Rat.castHom ℚ_[p]).toMonoidHom b)) = 1 :=
  Rat.hilbertSymbol_product_formula a b

/-- Since $(-1, -1)_\infty = -1$, the product of the $p$-adic symbols $(-1, -1)_p$ is $-1$. -/
theorem finprod_neg_one_neg_one :
    ∏ᶠ p : Nat.Primes,
      (haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
      padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-1))
        (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-1))) = -1 := by
  have h := (Rat.hilbertSymbol_product_formula (-1) (-1)).2
  have hr : realHilbertSymbol (Units.map (Rat.castHom ℝ).toMonoidHom (-1))
      (Units.map (Rat.castHom ℝ).toMonoidHom (-1)) = -1 :=
    realHilbertSymbol.eq_neg_one_iff_both_neg.2 (by simp)
  rw [hr] at h
  linarith

/-- In particular $(-1, -1)_p = -1$ for some prime $p$. -/
example : ∃ p : Nat.Primes,
    haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
    padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-1))
      (Units.map (Rat.castHom ℚ_[p]).toMonoidHom (-1)) ≠ 1 := by
  by_contra h
  push Not at h
  have h1 := finprod_neg_one_neg_one
  rw [finprod_eq_one_of_forall_eq_one h] at h1
  exact absurd h1 (by decide)

end HilbertSymbolProductFormulaTest
