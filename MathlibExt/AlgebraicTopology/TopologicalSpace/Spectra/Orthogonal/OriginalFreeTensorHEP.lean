/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamilyTensorImage
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.GeneratorsCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.FreeBoundarySmash
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction

/-!
# Homotopy extension for free orthogonal tensor generators

Every arrow in the native free-`I` family retains based homotopy extension
after right tensoring with an arbitrary orthogonal spectrum. The family is
the free coefficient image of the realized boundary inclusions, so its
coefficient extension property transfers through the tensor-right functor.
The smash braiding gives the corresponding left-tensor statement.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open PointedCGWH.Spectra.Orthogonal
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CategoryTheory.MonObj

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

namespace PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorHEP

private abbrev C := Actual.OrthogonalCarrier.{u, v}

/-- The complete original source carrier is the literal actual native carrier. -/
theorem sourceCarrier_eq_native : CanonicalSourceSmash.Carrier.{u, v} = C.{u, v} := rfl

/-- Both frames retain the same full original generator class and operator index. -/
theorem sourceI_eq_nativeI :
    HomotopicalAlgebra.EnrichedProjective.generators
      (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      PointedCGWH.realizedBoundaryInclusions.{u, v} =
    NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) := rfl

/-- The complete original free coefficient functor family, retaining every operator. -/
def originalFreeFunctors : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} →
    PointedCGWH.{u, v} ⥤ C.{u, v} := fun a => Free.functor a

/-- The actual original tensor-right functor is factored as one typed native value. -/
def originalTensorRight (N : C.{u, v}) : C.{u, v} ⥤ C.{u, v} := tensorRight N

/-- Opaque generic factoring retains the complete native right-smash HEP property. -/
def originalRightProperty (N : C.{u, v}) : MorphismProperty C.{u, v} :=
  PointedCGWH.EnrichedBasedHomotopyExtension.property.inverseImage (tensorRight N)

/-- The full original coefficient image uses the typed functor before family transport. -/
theorem originalCoefficientImage_HEP (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    (N : C.{u, v}) {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : PointedCGWH.realizedBoundaryInclusions i) :
    originalRightProperty N (Free.coefficientMap a i) :=
  OrthogonalIGeneratorProbe.NativeOriginalHEP.original_freeBoundary_smash_HEP a i hi N

/-- Every original free-I map has its HEP image under the same actual right tensor functor. -/
theorem originalFreeI_tensorRight_image (N : C.{u, v}) :
    NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) ≤
      originalRightProperty N := by
  change HomotopicalAlgebra.EnrichedProjective.generators
    (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    PointedCGWH.realizedBoundaryInclusions ≤ _
  rw [HomotopicalAlgebra.EnrichedProjective.generators_eq_coefficient_ofHoms]
  exact (MorphismProperty.ofHoms_le_iff
    (fun q : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} ×
      PointedCGWH.realizedBoundaryInclusions.toSet => Free.coefficientMap q.1 q.2.1.hom)
    (originalRightProperty N)).mpr (fun q => originalCoefficientImage_HEP q.1 N q.2.1.hom q.2.2)

/-- Every literal original native free-I map retains HEP after an arbitrary right spectrum. -/
theorem originalFreeI_rightTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (i ▷ N) :=
  (originalFreeI_tensorRight_image N) i hi

/-- The whole actual original braid gives HEP after every arbitrary left spectrum as well. -/
theorem originalFreeI_leftTensor_HEP (N : C.{u, v}) {K L : C.{u, v}}
    (i : K ⟶ L) (hi : NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (N ◁ i) :=
  CategoryTheory.MorphismProperty.AdjointFamilyTensorImage.leftTensor_of_right
    PointedCGWH.EnrichedBasedHomotopyExtension.property N i (originalFreeI_rightTensor_HEP N i hi)

end PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorHEP
