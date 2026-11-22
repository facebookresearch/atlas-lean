/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.OriginalFreeTensorHEP

/-!
# Orthogonal module frames and generator homotopy extension

Identifies the category structures used for orthogonal sphere modules and proves based homotopy
extension for both tensor orders of the level generating family. The tensor statements are
independent of the chosen ordinal bottom used by the stable model.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.ModuleSourceFrame.Orthogonal

private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
private abbrev H : MorphismProperty C.{u, v} := PointedCGWH.EnrichedBasedHomotopyExtension.property

/-- The actual source category retained before the caller's selected native instance frame. -/
@[instance_reducible]
def sourceCategoryFrame : Category C.{u, v} := inferInstance

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.monoidalCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmash.symmetricCategory
  PointedCGWH.Spectra.Orthogonal.CanonicalSourceSmashClosed.monoidalClosed
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexMonoidalCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexEnrichedOrdinaryCategory
  PointedCGWH.Spectra.Orthogonal.SphereSmashStructure.indexSymmetricCategory

/-- The original orthogonal stable model with the caller's chosen generator-cardinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.orthogonalModelCategory (B := B)

/-- The selected native caller category is the same actual enriched functor category. -/
@[instance_reducible]
def nativeCategoryFrame : Category C.{u, v} := inferInstance

omit B in
/-- The source and native caller category frames are equal as complete categories. -/
theorem categoryFrames_eq : sourceCategoryFrame.{u, v} = nativeCategoryFrame.{u, v} := rfl

omit B in
/-- The complete original I family has right-smash HEP in the original native module-source frame. -/
theorem originalI_rightTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : I i) : H (i ▷ N) :=
  PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorHEP.originalFreeI_rightTensor_HEP N i hi

omit B in
/-- The same full original family retains HEP in the other actual tensor order. -/
theorem originalI_leftTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : I i) : H (N ◁ i) :=
  PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorHEP.originalFreeI_leftTensor_HEP N i hi

end HomotopicalAlgebra.EnrichedProjective.Native.ModuleSourceFrame.Orthogonal
