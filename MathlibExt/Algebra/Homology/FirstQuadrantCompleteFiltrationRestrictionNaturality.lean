/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationRestriction

/-!
# Bicomplex naturality of complete-filtration restriction

The natural-index restriction of the complete horizontal-filtration diagram
and the original finite filtration diagram are functorial in a first-quadrant
bicomplex.  The objectwise complete/finite comparison isomorphisms assemble
into a natural isomorphism between these diagram-valued functors.
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

/-- First-quadrant bicomplexes mapped to the natural-index restriction of
their complete horizontal-filtration diagrams. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) where
  obj K := horizontalFiltrationNatToEIntFunctor ⋙
    (horizontalCompleteTotalFiltration K).diagram
  map f := Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
    (horizontalCompleteTotalFilteredObjectMap f).natTrans
  map_id K := by
    have h := congrArg CategoryTheory.FilteredObject.Hom.natTrans
      (horizontalCompleteTotalFilteredObjectFunctor.map_id K)
    change (horizontalCompleteTotalFilteredObjectMap (𝟙 K)).natTrans =
      CategoryTheory.FilteredObject.Hom.natTrans
        (𝟙 (horizontalCompleteTotalFilteredObject K)) at h
    change Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFilteredObjectMap (𝟙 K)).natTrans = 𝟙 _
    rw [h]
    rfl
  map_comp f g := by
    have h := congrArg CategoryTheory.FilteredObject.Hom.natTrans
      (horizontalCompleteTotalFilteredObjectFunctor.map_comp f g)
    change (horizontalCompleteTotalFilteredObjectMap (f ≫ g)).natTrans =
      CategoryTheory.FilteredObject.Hom.natTrans
        (horizontalCompleteTotalFilteredObjectMap f ≫
          horizontalCompleteTotalFilteredObjectMap g) at h
    change Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFilteredObjectMap (f ≫ g)).natTrans =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
          (horizontalCompleteTotalFilteredObjectMap f).natTrans ≫
        Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
          (horizontalCompleteTotalFilteredObjectMap g).natTrans
    rw [h]
    rfl

/-- First-quadrant bicomplexes mapped to their original finite horizontal-
filtration diagrams. -/
noncomputable def horizontalTotalFiltrationDiagramFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      (ℕ ⥤ ChainComplex C ℕ) where
  obj K := (horizontalTotalFiltration K).diagram
  map f := (horizontalTotalFilteredObjectMap f).natTrans
  map_id K := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (horizontalTotalFilteredObjectFunctor.map_id K)
  map_comp f g := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (horizontalTotalFilteredObjectFunctor.map_comp f g)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.obj K =
      horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalCompleteTotalFiltration K).diagram :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor.map f).app n =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f
        ((n : ℤ) : EInt) :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalTotalFiltrationDiagramFunctor.obj K =
      (horizontalTotalFiltration K).diagram :=
  rfl

omit [HasZeroObject C] in
@[simp]
theorem horizontalTotalFiltrationDiagramFunctor_map_app
    (f : K ⟶ L) (n : ℕ) :
    (horizontalTotalFiltrationDiagramFunctor.map f).app n =
      horizontalFilteredTotalComplexMapOfBicomplex f n :=
  rfl

/-- The complete/finite restriction comparison is natural in the
bicomplex. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionNatIso :
    horizontalCompleteTotalFiltrationNatRestrictionDiagramFunctor (C := C) ≅
      horizontalTotalFiltrationDiagramFunctor (C := C) :=
  NatIso.ofComponents horizontalCompleteTotalFiltrationNatRestrictionIso
    (by
      intro K L f
      apply NatTrans.ext
      funext n
      change horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            ((n : ℤ) : EInt) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L
            (n : ℤ) (Int.natCast_nonneg n)).hom =
        (horizontalCompleteFilteredTotalComplexFiniteIso K
            (n : ℤ) (Int.natCast_nonneg n)).hom ≫
          horizontalFilteredTotalComplexMapOfBicomplex f n
      simpa only [Int.toNat_natCast] using
        (horizontalCompleteFilteredTotalComplexFiniteIso_naturality f
          (n : ℤ) (Int.natCast_nonneg n)).symm)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionNatIso
      (C := C)).hom.app K =
      (horizontalCompleteTotalFiltrationNatRestrictionIso K).hom :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionNatIso_hom_app_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    ((horizontalCompleteTotalFiltrationNatRestrictionNatIso
      (C := C)).hom.app K).app n =
      (horizontalCompleteFilteredTotalComplexFiniteIso K
        (n : ℤ) (Int.natCast_nonneg n)).hom :=
  rfl

end HomologicalComplex₂

end
