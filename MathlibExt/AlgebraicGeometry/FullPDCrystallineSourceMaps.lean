/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules
public import MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps
public import MathlibExt.CategoryTheory.RingedSliceExtSourceMaps

/-!
# Original group maps on the full crystalline Ext basis

The full-basis coefficient maps are the sheafification of postcomposition
on the original finite group levels. Ext then precomposes by those same
sheaf maps, with the fixed target-multiplication scalar action.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FullPDCrystallineSourceMaps

open _root_.CategoryTheory Opposite
open FullPDCrystallineTests FullPDCrystallineSheaves FullPDCrystallineExtModules

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

/-- The original tower point map on each full-basis reduction. -/
def groupPresheafMap {G H : PDivisibleGroupSchemes.PDivisibleGroup S.left p}
    (f : PDivisibleGroupMaps.Hom p G H) :
    groupPresheaf p A S G ⟶ groupPresheaf p A S H :=
  Functor.whiskerLeft (reductions p A S).op
    (Functor.whiskerRight (PDivisibleGroupMaps.pointMap f)
      (CommGrpCat.toAddCommGrp ⋙ liftAbelianGroups))

/-- Sheafify precisely the original geometric group coefficient map. -/
def groupSheafMap {G H : PDivisibleGroupSchemes.PDivisibleGroup S.left p}
    (f : PDivisibleGroupMaps.Hom p G H) :
    groupSheaf p A S G ⟶ groupSheaf p A S H :=
  (presheafToSheaf (topology p A S) AddCommGrpCat.{1}).map
    (groupPresheafMap p A S f)

variable {F G : CoefficientSheaves p A S} (f : F ⟶ G)

/-- The native source map before module sheafification. -/
def sourcePresheafMap (n : ℕ) : coefficientPresheaf p A S G n ⟶
    coefficientPresheaf p A S F n :=
  MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap
    (topology p A S) (structureRingSheaf p A S) f n

/-- The actual module-sheafification map, with no selected module homomorphism. -/
def sourceSheafMap (n : ℕ) : coefficientModule p A S G n ⟶
    coefficientModule p A S F n :=
  (PresheafOfModules.sheafification (𝟙 (coefficientRing p A S).obj)).map
    (sourcePresheafMap p A S f n)

/-- The same map over the original thickening rings. -/
def nativeSourceMap (n : ℕ) : nativeModule p A S G n ⟶ nativeModule p A S F n :=
  (PresheafOfModules.restrictScalars (coefficientUnit p A S)).map
    ((SheafOfModules.forget (coefficientRing p A S)).map (sourceSheafMap p A S f n))

end MathlibExt.AlgebraicGeometry.FullPDCrystallineSourceMaps
