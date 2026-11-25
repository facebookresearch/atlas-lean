/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.IrreducibleSpecialization

@[expose] public section

universe u v w

-- Consumer with the original binders.
example {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ]
    (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map
      (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) :=
  MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    F hF

-- Boundary: the irreducibility hypothesis cannot be dropped. For the
-- constant polynomial `1`, the conclusion fails already over `ℚ`.
example : ¬ ∃ c : ℤ, c ≠ 0 ∧ ∀ (E : Type) [Field E] (φ : ℤ →+* E),
    φ c ≠ 0 → Irreducible (MvPolynomial.map φ (1 : MvPolynomial (Fin 1) ℤ)) := by
  rintro ⟨c, hc, h⟩
  have hc' : (Int.castRingHom ℚ) c ≠ 0 := Int.cast_ne_zero.mpr hc
  have hirr := h ℚ (Int.castRingHom ℚ) hc'
  rw [map_one] at hirr
  exact not_irreducible_one hirr
