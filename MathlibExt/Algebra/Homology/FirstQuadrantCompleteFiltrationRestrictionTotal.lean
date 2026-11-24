/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestrictionNaturality

/-!
# Total-complex compatibility of complete-filtration restriction

The finite horizontal-filtration diagram and the natural-index restriction
of the complete diagram both include naturally into the constant diagram on
the total complex.  The bicomplex-natural complete/finite restriction
isomorphism intertwines these two inclusion transformations.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The total complex of a first-quadrant bicomplex, regarded as a constant
natural-index diagram. -/
noncomputable def horizontalTotalComplexNatConstDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) :=
  HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
    Functor.const ℕ

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalComplexNatConstDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalTotalComplexNatConstDiagramFunctor.obj K =
      (Functor.const ℕ).obj (K.total (ComplexShape.down ℕ)) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalComplexNatConstDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalTotalComplexNatConstDiagramFunctor.map f).app n =
      total.map f (ComplexShape.down ℕ) :=
  rfl

/-- The finite horizontal-filtration diagrams include naturally into the
constant diagrams on total complexes. -/
noncomputable def horizontalTotalFiltrationDiagramToTotal :
    horizontalTotalFiltrationDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) where
  app K := (horizontalTotalFiltration K).ι
  naturality K L f := by
    apply NatTrans.ext
    funext n
    exact (horizontalTotalFilteredObjectMap f).comm n

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramToTotal_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalTotalFiltrationDiagramToTotal (C := C)).app K =
      (horizontalTotalFiltration K).ι :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramToTotal_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalTotalFiltrationDiagramToTotal (C := C)).app K).app n =
      horizontalFilteredTotalComplexToTotal K n :=
  rfl

/-- The natural-index restrictions of the complete horizontal filtrations
include naturally into the constant diagrams on total complexes. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ⟶
      horizontalTotalComplexNatConstDiagramFunctor (C := C) where
  app K := Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
    (horizontalCompleteTotalFiltration K).ι
  naturality K L f := by
    apply NatTrans.ext
    funext n
    change horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((n : ℤ) : EInt) ≫
        horizontalCompleteFilteredTotalToTotal L ((n : ℤ) : EInt) =
      horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt) ≫
        total.map f (ComplexShape.down ℕ)
    exact (horizontalCompleteTotalFilteredObjectMap f).comm
      ((n : ℤ) : EInt)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C)).app K =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFiltration K).ι :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C)).app K).app n =
      horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt) :=
  rfl

/-- The bicomplex-natural complete/finite restriction isomorphism preserves
the inclusions into total complexes. -/
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_comp_toTotal :
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso
        (C := C)).hom ≫
      horizontalTotalFiltrationDiagramToTotal (C := C) =
    horizontalCompleteTotalFiltrationNatRestrictionDiagramToTotal
      (C := C) := by
  apply NatTrans.ext
  funext K
  exact horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι K

end HomologicalComplex₂

end
