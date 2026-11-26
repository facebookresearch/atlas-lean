/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction
public import MathlibExt.CategoryTheory.NativeMappedUnitMonoids
public import MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

/-!
# Native Ind module inverse image on the original coefficient geometry

The inverse image is the prescribed compact-Yoneda functor. Rings are
its actual native mapMon images. The coefficient ring comparison is its
canonical mapMon unit, and both actions retain the original functor maps.
Derived inverse image is exact cochain localization of this source action.

Source: DK1311.2374v2 Sections2.2,3.3,4.10;
Mathlib56a005 native inverse image, braided mapMon and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafInverseImageModels
open NativeIndDifferentialContexts
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
open MathlibExt.CategoryTheory.NativeMappedUnitMonoids
open MathlibExt.CategoryTheory.NativeBimoduleScalarRestriction
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CompactSheafSource ℂ Y]
  [IndSpaceSource X] [IndSpaceSource Y]

local instance inverseModulePreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z] :
    Preadditive (IndSheaf ℂ Z) := Abelian.toPreadditive

class InverseMonoidalSource where
  ordinary : OrdinaryIndSource ℂ Y
  inverse : IndInverseImageSource ℂ f ordinary
  [braided : (indInverseImage ℂ f ordinary inverse).Braided]

attribute [instance_reducible, instance] InverseMonoidalSource.braided

variable (I : InverseMonoidalSource f)

local instance originalInverseBraided : (indInverseImage ℂ f I.ordinary I.inverse).Braided :=
  I.braided

abbrev originalInverse : IndSheaf ℂ X ⥤ IndSheaf ℂ Y := indInverseImage ℂ f I.ordinary I.inverse

abbrev inverseRing (R : Mon (IndSheaf ℂ X)) : Mon (IndSheaf ℂ Y) :=
  letI := I.braided
  (originalInverse f I).mapMon.obj R

variable (R : Mon (IndSheaf ℂ X))

structure IndModuleInverseSource where
  mapping : BimoduleMappingSource (indInverseImage ℂ f I.ordinary I.inverse)
    R (Mon.trivial (IndSheaf ℂ X))
  normalize : ScalarRestrictionSource
    (inverseRing f I R) (inverseRing f I (Mon.trivial (IndSheaf ℂ X)))
    (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y)) (𝟙 _)
    (letI := I.braided
     (mappedUnitIso (indInverseImage ℂ f I.ordinary I.inverse)).inv)

def indModuleInverse (S : IndModuleInverseSource f I R) :
    Bimod R (Mon.trivial (IndSheaf ℂ X)) ⥤
      Bimod (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y)) :=
  letI := I.braided
  S.mapping.functor ⋙ S.normalize.functor

local instance inverseBimodulePreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (A B : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod A B) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (S : IndModuleInverseSource f I R) [(indModuleInverse f I R S).Additive]
  (E : ExactImageSource (indModuleInverse f I R S))

def derivedIndModuleInverse :
    DerivedCategory (Bimod R (Mon.trivial (IndSheaf ℂ X))) ⥤
      DerivedCategory (Bimod (inverseRing f I R) (Mon.trivial (IndSheaf ℂ Y))) :=
  derivedExactImage (indModuleInverse f I R S) E

variable (T : Mon (IndSheaf ℂ X))
  (B : BimoduleMappingSource (originalInverse f I) R T) [B.functor.Additive]
  (BE : ExactImageSource B.functor)

/-- Both outer rings of the actual source bimodule are mapped by the same original inverse image. -/
def derivedIndBimoduleInverse : DerivedCategory (Bimod R T) ⥤
    DerivedCategory (Bimod (inverseRing f I R) (inverseRing f I T)) :=
  derivedExactImage B.functor BE

structure LeftUnitIndModuleInverseSource where
  mapping : BimoduleMappingSource (originalInverse f I) (Mon.trivial (IndSheaf ℂ X)) R
  normalize : ScalarRestrictionSource
    (inverseRing f I (Mon.trivial (IndSheaf ℂ X))) (inverseRing f I R)
    (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I R)
    (mappedUnitIso (originalInverse f I)).inv (𝟙 _)

def leftUnitIndModuleInverse (L : LeftUnitIndModuleInverseSource f I R) :
    Bimod (Mon.trivial (IndSheaf ℂ X)) R ⥤
      Bimod (Mon.trivial (IndSheaf ℂ Y)) (inverseRing f I R) :=
  L.mapping.functor ⋙ L.normalize.functor

end MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels
