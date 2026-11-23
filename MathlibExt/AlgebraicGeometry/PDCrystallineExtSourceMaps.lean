/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDCrystallineExtSheafification
public import MathlibExt.CategoryTheory.RingedSliceExtSourceMaps

/-!
# Source maps of the actual crystalline Ext module

Precompose each native slice Ext class by the original sheaf map.
It is linear for the original target-multiplication action, and its
restriction naturality is the native exact functor action on Ext; this is the generic
`MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap` on the nilpotent PD site.
Sheafification then produces the actual coefficient-module map.
This is the covariant map after the original Cartier-dual group map.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDCrystallineExtSourceMaps

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves
open PDCrystallineExtSheafification

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)
  {F G : CoefficientSheaves p A S} (f : F ⟶ G)

/-- The map of local Ext module presheaves given by precomposition with `f` on every slice. -/
def sourcePresheafMap (n : ℕ) : localExtModulePresheaf p A S G n ⟶
    localExtModulePresheaf p A S F n :=
  MathlibExt.CategoryTheory.RingedSliceExtSourceMaps.sourcePresheafMap
    (topology p A S) (structureRingSheaf p A S) f n

/-- Actual module-sheafification of this fixed source coefficient map. -/
def sourceSheafMap (n : ℕ) : moduleSheaf p A S G n ⟶ moduleSheaf p A S F n :=
  (PresheafOfModules.sheafification (𝟙 (coefficientRing p A S).obj)).map
    (sourcePresheafMap p A S f n)

end MathlibExt.AlgebraicGeometry.PDCrystallineExtSourceMaps
