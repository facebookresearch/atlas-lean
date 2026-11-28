/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Opposite/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Opposite
public import MathlibExt.CategoryTheory.DGSource.CochainBraiding
public import MathlibExt.CategoryTheory.DGSource.DGCategory

/-!
# Opposite differential graded categories

The opposite of a differential graded category is obtained from the opposite enriched category.
Its Hom complex from `op X` to `op Y` is the original Hom complex from `Y` to `X`. Composition
first uses the Koszul braiding to reverse the two homogeneous factors. Consequently, for degrees
`p` and `q`, opposite composition is `(-1)^(p*q)` times the original composition in reversed
order. These identifications let calculations in the opposite category use the same differential
and the signed composition formulas of the original category.

Mathlib supplies the opposite of a category enriched in a braided monoidal category. The
`SymmetricCategory` instance on cochain complexes and its Koszul sign are supplied by
`MathlibExt.CategoryTheory.DGSource.CochainBraiding`.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* `Mathlib.CategoryTheory.Enriched.Opposite`, for the opposite enriched category.
-/

public section

open CategoryTheory MonoidalCategory Opposite HomologicalComplex

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The Hom complex from `op X` to `op Y` in the opposite DG category is the Hom complex from
`Y` to `X` in the original category. -/
@[simp]
theorem dgHomComplex_op (X Y : C) :
    dgHomComplex R (op X) (op Y) = dgHomComplex R Y X := rfl

/-- The differential in the opposite DG category is the original differential with source and
target reversed. -/
@[simp]
theorem dgDifferential_op {X Y : C} (n : ℤ) (f : DGHom R n Y X) :
    dgDifferential (R := R) (C := Cᵒᵖ) n f = dgDifferential R n f := rfl

/-- The identity in the opposite DG category is the original identity. -/
@[simp]
theorem dgId_op (X : C) :
    dgId (R := R) (C := Cᵒᵖ) (op X) = dgId R X := by
  rw [dgId_def, dgId_def]
  congr 1

/-- On the bidegree-`(p,q)` summand, composition in the opposite DG category is composition in
the original category after swapping the two factors with the Koszul sign. -/
theorem dgCompMap_op (X Y Z : C) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = n) :
    dgCompMap (R := R) (C := Cᵒᵖ) (op X) (op Y) (op Z) p q n (by dsimp at h ⊢; omega) =
      (p * q).negOnePow •
        ((β_ ((dgHomComplex R Y X).X p) ((dgHomComplex R Z Y).X q)).hom ≫
          dgCompMap R Z Y X q p n (by dsimp at h ⊢; omega)) := by
  rw [dgCompMap_def, CategoryTheory.eComp_op_eq, HomologicalComplex.comp_f,
    ← Category.assoc]
  simp only [dgHomComplex_op]
  rw [braiding_eq_koszulBraiding, koszulBraiding_hom, ι_koszulBraidingHom,
    koszulBraidingSummand_def, Linear.units_smul_comp, Category.assoc, dgCompMap_def]

/-- Composition in the opposite DG category reverses the factors and contributes the Koszul
sign. The sign is the value of the cochain-complex braiding on the bidegree-`(p,q)` summand. -/
@[simp]
theorem dgComp_op {X Y Z : C} {p q n : ℤ} (f : DGHom R p Y X) (g : DGHom R q Z Y)
    (h : p + q = n) :
    dgComp (R := R) (C := Cᵒᵖ) f g h =
      (p * q).negOnePow • dgComp R g f (by omega : q + p = n) := by
  rw [← dgCompMap_tmul, ← dgCompMap_tmul,
    dgCompMap_op R X Y Z p q n (by dsimp; omega)]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply]

end MathlibExt.DGSource
