/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeSymmetricCofibrantTensorFlatness
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.FreeCellFlatness
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitModelChange
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalModuleSourceFrame

/-!
# Source coefficients and cellular comparisons for sphere modules

Uses the equality of stable and level cofibration classes to prove cofibrancy and coefficient
flatness for the generating endpoints, against weak maps with arbitrary endpoints. Based
homotopy extension, coproducts and small continuous ordinal compositions give the cellular
comparison closure.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.ModuleTransfer.NativeSources.Symmetric

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} := NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev H : MorphismProperty C.{u, v} := PointedCGWH.EnrichedBasedHomotopyExtension.property
private abbrev W [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :=
  NativeK.omegaTests (B := B) Actual.symmetricFamily.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

/-- The original symmetric stable model with the caller's chosen generator-cardinal bottom. -/
local instance originalStableModel : ModelCategory C.{u, v} :=
  StableModelConstruction.symmetricModelCategory (B := B)

/-- The two actual original free-I endpoints are cofibrant in the same original stable model. -/
theorem originalI_endpoints {K L : C.{u, v}} (i : K ⟶ L) (hi : I i) :
    IsCofibrant K ∧ IsCofibrant L := by
  have he := NativeK.levelI_generatorEndpoints (B := B) i hi
  have hCof := (StableModelConstruction.symmetric_cofibrations_eq_level (B := B)).symm
  exact ⟨(HomotopicalAlgebra.ModelCategory.isCofibrant_iff_of_cofibrations_eq
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B)
        (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      (StableModelConstruction.symmetricModelCategory (B := B)) hCof K).mp he.1,
    (HomotopicalAlgebra.ModelCategory.isCofibrant_iff_of_cofibrations_eq
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B)
        (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      (StableModelConstruction.symmetricModelCategory (B := B)) hCof L).mp he.2⟩

/-- Both genuine generator coefficients preserve the underlying weak map on arbitrary endpoints. -/
theorem originalI_coefficientFlatness :
    HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I := by
  intro Y Z f hf K L i hi
  obtain ⟨hK, hL⟩ := originalI_endpoints i hi
  exact ⟨
    PointedCGWH.Spectra.Symmetric.OriginalCofibrantTensorFlatness.originalStableCofibrantRightTensor_weak f K hf hK,
    PointedCGWH.Spectra.Symmetric.OriginalCofibrantTensorFlatness.originalStableCofibrantRightTensor_weak f L hf hL⟩

omit B in
/-- Every original free boundary has the actual based HEP; arbitrary left coefficients retain it. -/
theorem originalI_leftTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : I i) : H (N ◁ i) := by
  have hiH : H i :=
    PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension.originalFreeI_le_nativeHEP _ hi
  have hr : H (i ▷ N) :=
    PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmashHomotopyExtension.rightSmash_preserves_basedHEP i hiH N
  let e : CategoryTheory.Arrow.mk (i ▷ N) ≅ CategoryTheory.Arrow.mk (N ◁ i) :=
    CategoryTheory.Arrow.isoMk (β_ K N) (β_ L N) (BraidedCategory.braiding_naturality_left i N).symm
  exact (H.arrow_mk_iso_iff e).mp hr

/-- All actual coproduct maps of arbitrary-endpoint Omega equivalences are Omega equivalences. -/
theorem omegaCoproducts : W (B := B).IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J :=
    IsStableUnderCoproductsOfShape.mk (W := W (B := B)) J (by
      intro X Y _ _ f hf
      exact PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalCofansMap_omegaTests
        (Cofan.mk (∐ X) (Sigma.ι X)) (coproductIsCoproduct X)
        (Cofan.mk (∐ Y) (Sigma.ι Y)) (coproductIsCoproduct Y)
        f (CategoryTheory.Limits.Sigma.map f) (fun j => Sigma.ι_map f j) hf)

/-- The exact original cofans, HEP pushout cubes and permitted continuous ordinal comparisons. -/
theorem omegaCellClosure : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{_, _, v, t} (W (B := B)) H where
  coproducts_h := inferInstance
  cobase_h := inferInstance
  transfinite_h := inferInstance
  coproducts_w := omegaCoproducts
  pushout := by
    intro A X Z P A' X' Z' P' i z kX kZ i' z' kX' kZ' sq sq' hi hi'
      a b c p hI hZ hX hP ha hb hc
    exact PointedCGWH.Spectra.Symmetric.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
      i z kX kZ i' z' kX' kZ' sq sq' hi hi' a b c p hI hZ hX hP ha hb hc
  ordinal := by
    intro J _ _ _ _ _ F G _ _ α hF hG hα cF cG hcF hcG d hd
    exact PointedCGWH.Spectra.StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests
      Actual.symmetricFamily F G α hF hG hα cF cG hcF hcG d hd

/-- The same certificate is expressed in the literal five-class stable weak dictionary. -/
theorem originalStableCellClosure :
    HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{_, _, v, t} (weakEquivalences C.{u, v}) H := by
  rw [(StableModelConstruction.symmetric_five_classes (B := B)).1]
  exact omegaCellClosure

end HomotopicalAlgebra.ModuleTransfer.NativeSources.Symmetric

namespace HomotopicalAlgebra.ModuleTransfer.NativeSources.Orthogonal

private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} :=
  NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
private abbrev H : MorphismProperty C.{u, v} := PointedCGWH.EnrichedBasedHomotopyExtension.property
private abbrev W [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] :=
  NativeK.omegaTests (B := B) Actual.orthogonalFamily.{u, v}

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

/-- Both original orthogonal free-I endpoints retain their original stable cofibrancy. -/
theorem originalI_endpoints {K L : C.{u, v}} (i : K ⟶ L) (hi : I i) :
    IsCofibrant K ∧ IsCofibrant L := by
  have he := NativeK.levelI_generatorEndpoints (B := B) i hi
  have hCof := (StableModelConstruction.orthogonal_cofibrations_eq_level (B := B)).symm
  exact ⟨(HomotopicalAlgebra.ModelCategory.isCofibrant_iff_of_cofibrations_eq
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B)
        (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      (StableModelConstruction.orthogonalModelCategory (B := B)) hCof K).mp he.1,
    (HomotopicalAlgebra.ModelCategory.isCofibrant_iff_of_cofibrations_eq
      (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (B := B)
        (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      (StableModelConstruction.orthogonalModelCategory (B := B)) hCof L).mp he.2⟩

/-- Every arbitrary-endpoint weak coefficient map is weak after either original free-I coefficient. -/
theorem originalI_coefficientFlatness :
    HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I := by
  intro Y Z f hf K L i hi
  obtain ⟨hK, hL⟩ := originalI_endpoints i hi
  have leftK :=
    PointedCGWH.Spectra.Orthogonal.OriginalCofibrantFlatnessComplete.originalStableCofibrantSmash_weak f K hf hK
  have leftL :=
    PointedCGWH.Spectra.Orthogonal.OriginalCofibrantFlatnessComplete.originalStableCofibrantSmash_weak f L hf hL
  exact ⟨HomotopicalAlgebra.TensorFlatnessOfReplacementCounits.rightTensor_weak_of_leftTensor f K leftK,
    HomotopicalAlgebra.TensorFlatnessOfReplacementCounits.rightTensor_weak_of_leftTensor f L leftL⟩

omit B in
/-- The whole actual free-I member is the original right-smash HEP map. -/
theorem originalI_rightTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : I i) : H (i ▷ N) :=
  HomotopicalAlgebra.EnrichedProjective.Native.ModuleSourceFrame.Orthogonal.originalI_rightTensor_HEP N i hi

omit B in
/-- The same original braid gives arbitrary left-coefficient HEP without scalar cofibrancy. -/
theorem originalI_leftTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : I i) : H (N ◁ i) := by
  let e : CategoryTheory.Arrow.mk (i ▷ N) ≅ CategoryTheory.Arrow.mk (N ◁ i) :=
    CategoryTheory.Arrow.isoMk (β_ K N) (β_ L N) (BraidedCategory.braiding_naturality_left i N).symm
  exact (H.arrow_mk_iso_iff e).mp (originalI_rightTensor_HEP N i hi)

/-- Arbitrary-endpoint weak coproduct comparisons use the original public orthogonal theorem. -/
theorem omegaCoproducts : W (B := B).IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J :=
    IsStableUnderCoproductsOfShape.mk (W := W (B := B)) J (by
      intro X Y _ _ f hf
      exact PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure.originalCoproductMap_omegaTests f hf)

/-- The original orthogonal pushouts/cofans and both controlled continuous diagrams supply cell closure. -/
theorem omegaCellClosure : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{_, _, v, t} (W (B := B)) H where
  coproducts_h := inferInstance
  cobase_h := inferInstance
  transfinite_h := inferInstance
  coproducts_w := omegaCoproducts
  pushout := by
    intro A X Z P A' X' Z' P' i z kX kZ i' z' kX' kZ' sq sq' hi hi'
      a b c p hI hZ hX hP ha hb hc
    exact PointedCGWH.Spectra.Orthogonal.OriginalHEPOmegaClosure.originalHEPPushoutComparison_omegaTests
      i z kX kZ i' z' kX' kZ' sq sq' hi hi' a b c p hI hZ hX hP ha hb hc
  ordinal := by
    intro J _ _ _ _ _ F G _ _ α hF hG hα cF cG hcF hcG d hd
    exact PointedCGWH.Spectra.StableHEPOrdinalWeakComparison.originalHEPOrdinalSmallComparison_omegaTests
      Actual.orthogonalFamily F G α hF hG hα cF cG hcF hcG d hd

/-- The literal full original stable weak class is the original Omega class. -/
theorem originalStableCellClosure :
    HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{_, _, v, t} (weakEquivalences C.{u, v}) H := by
  rw [(StableModelConstruction.orthogonal_five_classes (B := B)).1]
  exact omegaCellClosure

end HomotopicalAlgebra.ModuleTransfer.NativeSources.Orthogonal
