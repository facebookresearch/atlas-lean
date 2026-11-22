/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.OriginalFreeTensorHEP
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.GeneratorsCoefficient
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarKanClosedEmbedding

/-!
# Closed embeddings of the complete original orthogonal free-I tensor family

The whole actual free-smash/scalar-Kan comparison transports the closed
embedding proved for each original coefficient boundary and arbitrary tensor
factor. Family transport then retains every original operator, endpoint and
native evaluation. The tensor order is changed by the actual whole braid.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra Topology
open PointedCGWH.Spectra.Orthogonal
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed CategoryTheory.MonObj

attribute [local instance] CanonicalSourceSmash.monoidalCategory
  CanonicalSourceSmash.symmetricCategory CanonicalSourceSmashClosed.monoidalClosed
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer
  SphereSmashStructure.indexCategory SphereSmashStructure.indexMonoidalCategory
  SphereSmashStructure.indexEnrichedOrdinaryCategory SphereSmashStructure.indexSymmetricCategory

namespace PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorClosedEmbedding

open HomotopicalAlgebra.EnrichedProjective.Native.ScalarKanClosedEmbedding

private abbrev C := Actual.OrthogonalCarrier.{u, v}

/-- Each original raw-index free boundary tensor is closed at every original operator evaluation. -/
theorem originalRawCoefficient_component (r : CategoryTheory.Spectra.OrthogonalIndex)
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom
      (component
        ((Free.coefficientMap (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex r) i) ▷ N) b).right) := by
  have ht : evaluatedClosed b ((OrthogonalIGeneratorProbe.NativeEvaluatedTarget.target r N).map i) := by
    rw [OrthogonalIGeneratorProbe.NativeEvaluatedTarget.target_map]
    exact originalBoundary_mem_evaluatedClosed
      (FunctionSpectrum.RightShift.indexShift.{u, v} r) i hi N b
  have hs : evaluatedClosed b ((OrthogonalIGeneratorProbe.NativeEvaluatedFields.source r N).map i) :=
    evaluatedClosed_ofArrowIso (OrthogonalIGeneratorProbe.NativeHEPJoin.arrow r N i) b ht
  rw [OrthogonalIGeneratorProbe.NativeEvaluatedFields.source_map] at hs
  exact (evaluatedClosed_iff _ b).mp hs

/-- Every original operator free boundary tensor is closed at every original evaluation. -/
theorem originalCoefficient_component (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (component ((Free.coefficientMap a i) ▷ N) b).right) := by
  have h := originalRawCoefficient_component a.asIndex i hi N b
  rw [OrthogonalIGeneratorProbe.NativeOriginalHEP.ofIndex_asIndex] at h
  exact h

/-- The original right tensor family is measured at the same actual native operator. -/
def originalRightProperty (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    MorphismProperty C.{u, v} :=
  (evaluatedClosed b).inverseImage (tensorRight N)

/-- Every original free coefficient boundary belongs to its actual evaluated right-tensor closed class. -/
theorem originalCoefficient_image (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    {K L : PointedCGWH.{u, v}} (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    originalRightProperty N b (Free.coefficientMap a i) :=
  (evaluatedClosed_iff _ b).mpr (originalCoefficient_component a i hi N b)

/-- The complete original native I-family retains its evaluated closed class after every arbitrary right tensor. -/
theorem originalI_tensorRight_image (N : C.{u, v})
    (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) ≤ originalRightProperty N b := by
  change HomotopicalAlgebra.EnrichedProjective.generators
    (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) PointedCGWH.realizedBoundaryInclusions ≤ _
  rw [HomotopicalAlgebra.EnrichedProjective.generators_eq_coefficient_ofHoms]
  exact (MorphismProperty.ofHoms_le_iff
    (fun q : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} ×
      PointedCGWH.realizedBoundaryInclusions.toSet => Free.coefficientMap q.1 q.2.1.hom)
    (originalRightProperty N b)).mpr (fun q => originalCoefficient_image q.1 q.2.1.hom q.2.2 N b)

/-- Every literal original I map is pointwise closed after the actual right tensor with any native spectrum. -/
theorem originalI_rightTensor_component {K L : C.{u, v}} (i : K ⟶ L)
    (hi : NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) i)
    (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (component (i ▷ N) b).right) :=
  (evaluatedClosed_iff _ b).mp
    (originalI_tensorRight_image N b i hi)

/-- Every literal original I map is pointwise closed in the other tensor order by its original full braid. -/
theorem originalI_leftTensor_component {K L : C.{u, v}} (i : K ⟶ L)
    (hi : NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) i)
    (N : C.{u, v}) (b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (component (N ◁ i) b).right) := by
  apply (evaluatedClosed_iff _ b).mp
  exact CategoryTheory.MorphismProperty.AdjointFamilyTensorImage.leftTensor_of_right (evaluatedClosed b) N i
    ((evaluatedClosed_iff _ b).mpr (originalI_rightTensor_component i hi N b))

end PointedCGWH.Spectra.Orthogonal.OriginalFreeTensorClosedEmbedding
