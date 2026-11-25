/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPositiveStep

/-!
# The positive total-homology filtration square

A bicomplex map induces, at every positive column, a commutative square
between the corresponding consecutive complete total-homology filtration
steps.  The vertical maps are transported from the finite filtered-object
functor.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The map on the preceding complete homology-filtration stages in a
positive column, transported from natural index `p - 1`. -/
noncomputable def horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) :=
  (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
      K (p + q) p hp).hom ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans.app
      (p - 1) ≫
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
      L (p + q) p hp).inv

/-- The map on the current complete homology-filtration stages in a positive
column, transported from natural index `p`. -/
noncomputable def horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        (((p : ℤ) : EInt)) :=
  (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
      (p + q)).hom.app p ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans.app p ≫
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
      (p + q)).inv.app p

@[simp]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).hom ≫
        ((horizontalFiniteTotalHomologyFilteredObjectFunctor
          (p + q)).map f).natTrans.app (p - 1) ≫
        (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          L (p + q) p hp).inv :=
  rfl

@[simp]
theorem horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq
    (f : K ⟶ L) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).hom.app p ≫
        ((horizontalFiniteTotalHomologyFilteredObjectFunctor
          (p + q)).map f).natTrans.app p ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso L
          (p + q)).inv.app p :=
  rfl

/-- For a positive column, a bicomplex map commutes with the consecutive
complete total-homology filtration step. -/
theorem horizontalTotalHomologyFiltrationStepMap_naturality_of_pos
    (f : K ⟶ L) (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
  let a : (p - 1 : ℕ) ⟶ p := homOfLE (Nat.sub_le p 1)
  let DK : ℕ ⥤ C := (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram
  let DL : ℕ ⥤ C := (horizontalFiniteTotalHomologyFiltration L (p + q)).diagram
  let eKPrev : (horizontalTotalHomologyFiltration K (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅ DK.obj (p - 1) :=
    horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K (p + q) p hp
  let eLPrev : (horizontalTotalHomologyFiltration L (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅ DL.obj (p - 1) :=
    horizontalPositivePrevCompleteFiniteHomologyFiltrationIso L (p + q) p hp
  let eKCurr : (horizontalTotalHomologyFiltration K (p + q)).obj
      (((p : ℤ) : EInt)) ≅ DK.obj p :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).app p
  let eLCurr : (horizontalTotalHomologyFiltration L (p + q)).obj
      (((p : ℤ) : EInt)) ≅ DL.obj p :=
    (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)).app p
  let τ : DK ⟶ DL :=
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor (p + q)).map f).natTrans
  let dK : DK.obj (p - 1) ⟶ DK.obj p := DK.map a
  let dL : DL.obj (p - 1) ⟶ DL.obj p := DL.map a
  have hK :
      horizontalTotalHomologyFiltrationStepMap K p q ≫ eKCurr.hom =
        eKPrev.hom ≫ dK :=
    horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
      K p q hp
  have hL :
      dL ≫ eLCurr.inv =
        eLPrev.inv ≫ horizontalTotalHomologyFiltrationStepMap L p q :=
    horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv
      L p q hp
  have hm : dK ≫ τ.app p = τ.app (p - 1) ≫ dL :=
    τ.naturality a
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq]
  change
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        (eKCurr.hom ≫ τ.app p ≫ eLCurr.inv) =
      (eKPrev.hom ≫ τ.app (p - 1) ≫ eLPrev.inv) ≫
        horizontalTotalHomologyFiltrationStepMap L p q
  calc
    horizontalTotalHomologyFiltrationStepMap K p q ≫
          (eKCurr.hom ≫ τ.app p ≫ eLCurr.inv) =
        (horizontalTotalHomologyFiltrationStepMap K p q ≫ eKCurr.hom) ≫
          τ.app p ≫ eLCurr.inv := by
      simp only [Category.assoc]
    _ = (eKPrev.hom ≫ dK) ≫ τ.app p ≫ eLCurr.inv := by
      rw [hK]
    _ = eKPrev.hom ≫ (dK ≫ τ.app p) ≫ eLCurr.inv := by
      simp only [Category.assoc]
    _ = eKPrev.hom ≫ (τ.app (p - 1) ≫ dL) ≫ eLCurr.inv := by
      rw [hm]
    _ = (eKPrev.hom ≫ τ.app (p - 1)) ≫
        (dL ≫ eLCurr.inv) := by
      simp only [Category.assoc]
    _ = (eKPrev.hom ≫ τ.app (p - 1)) ≫
        (eLPrev.inv ≫ horizontalTotalHomologyFiltrationStepMap L p q) := by
      rw [hL]
    _ = (eKPrev.hom ≫ τ.app (p - 1) ≫ eLPrev.inv) ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
      simp only [Category.assoc]

end HomologicalComplex₂

end
