/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.OddPrimeFromReciprocity

/-!
# Tests for the odd prime given by Hilbert reciprocity
-/

set_option autoImplicit false

@[expose] public section

namespace OddPrimeFromReciprocityTest

/-- The statement, with the source's binders. -/
example {a b : ℚˣ} (hb : 0 < (b : ℚ))
    (h2 : padicHilbertSymbol 2 (Units.map (Rat.castHom ℚ_[2]).toMonoidHom a)
      (Units.map (Rat.castHom ℚ_[2]).toMonoidHom b) = -1) :
    ∃ ℓ : Nat.Primes, (ℓ : ℕ) ≠ 2 ∧
      haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
      padicHilbertSymbol ℓ (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom a)
        (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom b) = -1 :=
  Rat.exists_odd_prime_padicHilbertSymbol_eq_neg_one hb h2

/-- $3$ has norm $1$ in $\mathbb{Z}_2$. -/
theorem norm_three : ‖((3 : ℕ) : ℤ_[2])‖ = 1 :=
  PadicInt.norm_natCast_eq_one_iff.2 (by decide)

/-- $(-1, 3)_2 = -1$, by the $2$-adic formula: $\varepsilon(-1)\varepsilon(3) = 1$. -/
theorem neg_one_three_two :
    padicHilbertSymbol 2 (Units.map (Rat.castHom ℚ_[2]).toMonoidHom (-1))
      (Units.map (Rat.castHom ℚ_[2]).toMonoidHom (Units.mk0 3 (by norm_num))) = -1 := by
  rw [padicHilbertSymbol.eq_formula_two _ _ 0 0 (-1) (PadicInt.isUnit_iff.2 norm_three).unit
    (by simp) (by simp; norm_cast)]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, IsUnit.unit_spec, map_natCast]
  decide

/-- So $(-1, 3)_\ell = -1$ at some odd prime $\ell$ (in fact $\ell = 3$). -/
example : ∃ ℓ : Nat.Primes, (ℓ : ℕ) ≠ 2 ∧
    haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
    padicHilbertSymbol ℓ (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom (-1))
      (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom (Units.mk0 3 (by norm_num))) = -1 :=
  Rat.exists_odd_prime_padicHilbertSymbol_eq_neg_one (by norm_num) neg_one_three_two

end OddPrimeFromReciprocityTest
