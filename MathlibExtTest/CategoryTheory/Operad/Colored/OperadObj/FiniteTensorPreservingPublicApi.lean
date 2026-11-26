/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.FiniteTensorPreserving

/-!
# Focused O7E finite-tensor-preserving map public-contract packet

Pins the stable downstream-facing contracts for mapping colored
operads along a finite-tensor-preserving functor: the comparison
isos, mapped unit/substitution, and the map functor with its
projection formulas.
-/

open CategoryTheory
open CategoryTheory.Operad

universe uColor v₁ v₂ u₁ u₂

variable {Color : Type uColor} {V : Type u₁} {W : Type u₂}
  [Category.{v₁} V] [Category.{v₂} W]
  [FiniteTensor V] [FiniteTensor W]

-- Empty-family and comparison isos.
noncomputable example (F : V ⥤ W) :
    (FiniteFamily.empty : FiniteFamily W) ≅
      (FiniteFamily.map F).obj
        (FiniteFamily.empty : FiniteFamily V) :=
  ColoredOperadObj.MapData.emptyFamilyIso F

noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) (X : FiniteFamily V) :
    (FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W)).obj X ≅
      (FiniteTensor.tensor (V := V) ⋙ F).obj X :=
  ColoredOperadObj.MapData.comparisonIsoApp p X

noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) :
    (FiniteTensor.tensor (V := W)).obj
          (FiniteFamily.empty : FiniteFamily W) ≅
      F.obj ((FiniteTensor.tensor (V := V)).obj
        (FiniteFamily.empty : FiniteFamily V)) :=
  ColoredOperadObj.MapData.unitSourceIso p

-- Factors iso and naturality.
noncomputable example (F : V ⥤ W)
    (O : ColoredSymmetricCollection Color V)
    (X : ColoredSubstitutionData Color) :
    (FiniteFamily.map F).obj
          ((ColoredOperadObj.substitutionFactors O).obj X) ≅
      (ColoredOperadObj.substitutionFactors (O ⋙ F)).obj X :=
  ColoredOperadObj.MapData.factorsIso F O X

example {F : V ⥤ W} {O : ColoredSymmetricCollection Color V}
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (FiniteFamily.map F).map
          ((ColoredOperadObj.substitutionFactors O).map f) ≫
        (ColoredOperadObj.MapData.factorsIso F O Y).hom =
      (ColoredOperadObj.MapData.factorsIso F O X).hom ≫
        (ColoredOperadObj.substitutionFactors (O ⋙ F)).map f :=
  ColoredOperadObj.MapData.factorsIso_naturality f

example {F : V ⥤ W} {O : ColoredSymmetricCollection Color V}
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (ColoredOperadObj.MapData.factorsIso F O X).inv ≫
        (FiniteFamily.map F).map
          ((ColoredOperadObj.substitutionFactors O).map f) =
      (ColoredOperadObj.substitutionFactors (O ⋙ F)).map f ≫
        (ColoredOperadObj.MapData.factorsIso F O Y).inv :=
  ColoredOperadObj.MapData.factorsIso_inv_naturality f

-- Source comparison iso/hom and naturality.
noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F)
    (O : ColoredSymmetricCollection Color V)
    (X : ColoredSubstitutionData Color) :
    (FiniteTensor.tensor (V := W)).obj
          ((ColoredOperadObj.substitutionFactors (O ⋙ F)).obj X) ≅
      F.obj ((FiniteTensor.tensor (V := V)).obj
        ((ColoredOperadObj.substitutionFactors O).obj X)) :=
  ColoredOperadObj.MapData.sourceComparisonIso p O X

noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F)
    (O : ColoredSymmetricCollection Color V)
    (X : ColoredSubstitutionData Color) :
    (FiniteTensor.tensor (V := W)).obj
          ((ColoredOperadObj.substitutionFactors (O ⋙ F)).obj X) ⟶
      F.obj ((FiniteTensor.tensor (V := V)).obj
        ((ColoredOperadObj.substitutionFactors O).obj X)) :=
  ColoredOperadObj.MapData.sourceComparisonHom p O X

example {F : V ⥤ W} {O : ColoredSymmetricCollection Color V}
    (p : FiniteTensor.Preserving F)
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y) :
    (ColoredOperadObj.substitutionSource (O ⋙ F)).map f ≫
        ColoredOperadObj.MapData.sourceComparisonHom p O Y =
      ColoredOperadObj.MapData.sourceComparisonHom p O X ≫
        F.map
          ((ColoredOperadObj.substitutionSource O).map f) :=
  ColoredOperadObj.MapData.sourceComparisonHom_naturality p f

-- Mapped unit and substitution.
noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) :
    ColoredOperadUnit (O.toCollection ⋙ F) :=
  ColoredOperadObj.MapData.mappedUnit p O

noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) :
    ColoredOperadSubstitution (O.toCollection ⋙ F) :=
  ColoredOperadObj.MapData.mappedSubstitution p O

-- Map functor and projections.
noncomputable example {F : V ⥤ W}
    (p : FiniteTensor.Preserving F) :
    ColoredOperadObj Color V ⥤ ColoredOperadObj Color W :=
  ColoredOperadObj.mapFunctor p

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) :
    ((ColoredOperadObj.mapFunctor p).obj O).toCollection =
      O.toCollection ⋙ F :=
  ColoredOperadObj.mapFunctor_obj_toCollection p O

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (P : ColoredProfile Color) :
    ((ColoredOperadObj.mapFunctor p).obj O).toCollection.obj P =
      F.obj (O.toCollection.obj P) :=
  ColoredOperadObj.mapFunctor_obj_toCollection_obj p O P

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) :
    ((ColoredOperadObj.mapFunctor p).obj O).unit =
      ColoredOperadObj.MapData.mappedUnit p O :=
  ColoredOperadObj.mapFunctor_obj_unit p O

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (c : Color) :
    ((ColoredOperadObj.mapFunctor p).obj O).unit c =
      (ColoredOperadObj.MapData.unitSourceIso p).hom ≫
        F.map (O.unit c) :=
  ColoredOperadObj.mapFunctor_obj_unit_apply p O c

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) :
    ((ColoredOperadObj.mapFunctor p).obj O).subst =
      ColoredOperadObj.MapData.mappedSubstitution p O :=
  ColoredOperadObj.mapFunctor_obj_subst p O

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V)
    (X : ColoredSubstitutionData Color) :
    ((ColoredOperadObj.mapFunctor p).obj O).subst.app X =
      ColoredOperadObj.MapData.sourceComparisonHom p O.toCollection X ≫
        F.map (O.subst.app X) :=
  ColoredOperadObj.mapFunctor_obj_subst_app p O X

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    {O P : ColoredOperadObj Color V} (f : O ⟶ P) :
    ((ColoredOperadObj.mapFunctor p).map f).toCollectionHom =
      Functor.whiskerRight f.toCollectionHom F :=
  ColoredOperadObj.mapFunctor_map_toCollectionHom p f

example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    {O P : ColoredOperadObj Color V} (f : O ⟶ P)
    (X : ColoredProfile Color) :
    ((ColoredOperadObj.mapFunctor p).map f).toCollectionHom.app X =
      F.map (f.toCollectionHom.app X) :=
  ColoredOperadObj.mapFunctor_map_toCollectionHom_app p f X

-- Shared source naturality is available from the provider alone.
example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    {C D : ColoredSymmetricCollection Color V} (α : C ⟶ D)
    (X : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.sourceHom (Functor.whiskerRight α F) X ≫
        ColoredOperadObj.MapData.sourceComparisonHom p D X =
      ColoredOperadObj.MapData.sourceComparisonHom p C X ≫
        F.map (ColoredOperadObj.HomData.sourceHom α X) :=
  ColoredOperadObj.MapData.sourceComparisonHom_collection_naturality p α X

-- The canonical application rule preserves the original simp normal form.
example {F : V ⥤ W} (p : FiniteTensor.Preserving F)
    (O : ColoredOperadObj Color V) (X : ColoredSubstitutionData Color) :
    ((ColoredOperadObj.mapFunctor p).obj O).subst.app X =
      ColoredOperadObj.MapData.sourceComparisonHom p O.toCollection X ≫
        F.map (O.subst.app X) := by
  simp
