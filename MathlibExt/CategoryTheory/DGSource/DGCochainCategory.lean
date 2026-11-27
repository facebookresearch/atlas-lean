/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/CochainComplex/Basic.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.LinearHomComplexEnrichment
public import MathlibExt.CategoryTheory.DGSource.DGCategory

/-!
# Cochain complexes as a differential graded category

Cochain complexes in an `R`-linear preadditive category are enriched in cochain complexes of
`R`-modules through `CochainComplex.linearHomComplex`, so they form a differential graded category.
This file evaluates the differential graded operations of `MathlibExt/CategoryTheory/DGSource/DGCategory.lean`
on that example: the degree-`n` morphisms are the degree-`n` cochains, the differential is Mathlib's
signed `CochainComplex.HomComplex.δ`, the identity is the identity cochain, and composition is
composition of cochains with the Koszul sign.

That sign is the whole content of the comparison.  A differential graded category composes
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)` while composition of cochains is a closed map out of
`Hom(Y, Z) ⊗ Hom(X, Y)`, and interchanging the two factors of a tensor product of complexes is
the Koszul braiding.  Hence a degree-`p` cochain `z₁` followed by a degree-`q` cochain `z₂`
composes to `(-1) ^ (p * q) • z₁.comp z₂`.  This is the bridge between Mathlib's enriched factor
order and Keller's untwisted operation `m₂ (g, f) = g ∘ f`, and it is what fixes the sign
conventions of every later differential graded construction.

## Main results

* `MathlibExt.DGSource.dgDifferential_linearHomComplex`, `MathlibExt.DGSource.dgId_linearHomComplex` and
  `MathlibExt.DGSource.dgComp_linearHomComplex`: the differential, identity and composition of this
  differential graded category.
* `MathlibExt.DGSource.xIsoOfEq_hom_v` and `MathlibExt.DGSource.dgComp_v`: component formulas for degree transport and
  composition.

## Main definitions

* `MathlibExt.DGSource.cochainEval`: evaluation of cochains of complexes of modules at an element of the
  source, as a linear map.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex HomologicalComplex

namespace MathlibExt.DGSource

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The differential of the differential graded category of cochain complexes is the signed
differential `δ` of cochains. -/
@[simp]
theorem dgDifferential_linearHomComplex {F G : CochainComplex C ℤ} (n : ℤ)
    (z : DGHom R n F G) : dgDifferential R n z = δ n (n + 1) z :=
  linearHomComplex_d_hom_apply R F G n (n + 1) z

/-- The identity of the differential graded category of cochain complexes is the identity
cochain. -/
@[simp]
theorem dgId_linearHomComplex (F : CochainComplex C ℤ) :
    dgId R F = (Cochain.ofHom (𝟙 F) : ModuleCat.of R (Cochain F F 0)) := by
  rw [dgId_def, linearHomComplexEnrichedCategory_eId, linearHomComplexUnit_f_zero_apply,
    one_smul]

/-- Composition in the differential graded category of cochain complexes is composition of
cochains, carrying the Koszul sign which converts Mathlib's enriched factor order into Keller's
untwisted operation. -/
@[simp]
theorem dgComp_linearHomComplex {F G K : CochainComplex C ℤ} {p q n : ℤ}
    (z₁ : DGHom R p F G) (z₂ : DGHom R q G K) (h : p + q = n) :
    dgComp R z₁ z₂ h =
      ((p * q).negOnePow • Cochain.comp (z₁ : Cochain F G p) (z₂ : Cochain G K q) h :
        ModuleCat.of R (Cochain F K n)) := by
  have hmap : dgCompMap R F G K p q n h =
      (p * q).negOnePow •
        ((β_ ((linearHomComplex R F G).X p) ((linearHomComplex R G K).X q)).hom ≫
          cochainCompTensor R F G K q p n (by dsimp; omega)) := by
    rw [dgCompMap_def, linearHomComplexEnrichedCategory_eComp]
    exact ι_linearHomComplexEnrichedComp R F G K p q n h
  rw [← dgCompMap_tmul, hmap]
  exact cochainCompTensor_braiding_tmul R F G K p q n h z₁ z₂

/-- Degree transport of a cochain does not change its components. -/
theorem xIsoOfEq_hom_v {K L : CochainComplex C ℤ} {a b : ℤ} (h : a = b)
    (z : DGHom R a K L) (p q : ℤ) (hpq : p + b = q) :
    (((dgHomComplex R K L).XIsoOfEq h).hom z : Cochain K L b).v p q hpq =
      (z : Cochain K L a).v p q (by omega) := by
  subst h
  rfl

/-- The component of the DG composition of cochains is their componentwise composition with
the Koszul sign. -/
theorem dgComp_v {K L M : CochainComplex C ℤ} {a b c : ℤ} (z₁ : DGHom R a K L)
    (z₂ : DGHom R b L M) (h : a + b = c) (x y w : ℤ) (h₁ : x + a = y) (h₂ : y + b = w) :
    (dgComp R z₁ z₂ h : Cochain K M c).v x w (by omega) =
      (a * b).negOnePow • ((z₁ : Cochain K L a).v x y h₁ ≫ (z₂ : Cochain L M b).v y w h₂) := by
  rw [dgComp_linearHomComplex, Cochain.units_smul_v]
  exact congrArg _ (Cochain.comp_v (z₁ : Cochain K L a) (z₂ : Cochain L M b) h x y w h₁ h₂)

/-- **Evaluation** of degree-`p` cochains between complexes of `R`-modules at an element `x` of
degree `n` of the source, as an `R`-linear map to the degree-`q` part of the target. -/
noncomputable def cochainEval {K L : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ} (x : K.X n)
    (p q : ℤ) (h : n + p = q) : DGHom R p K L →ₗ[R] L.X q where
  toFun z := ((z : Cochain K L p).v n q h).hom x
  map_add' z z' := congrArg (fun φ ↦ ModuleCat.Hom.hom φ x) (Cochain.add_v z z' n q h)
  map_smul' r z := congrArg (fun φ ↦ ModuleCat.Hom.hom φ x) (Cochain.smul_v r z n q h)

/-- Evaluating a cochain at `x` applies its component out of the degree of `x`. -/
@[simp]
theorem cochainEval_apply {K L : CochainComplex (ModuleCat.{v} R) ℤ} {n : ℤ} (x : K.X n)
    (p q : ℤ) (h : n + p = q) (z : DGHom R p K L) :
    cochainEval R x p q h z = ((z : Cochain K L p).v n q h).hom x :=
  (rfl)

end MathlibExt.DGSource
