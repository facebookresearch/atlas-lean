/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTensorClosedEmbedding

/-!
# Pointed realized sources along selected cofibration chains

The established compatibility lemmas use the stronger closed-chain source
engine. Their original cardinal, generator family, diagram and public
signatures are retained; the generic source argument is implemented once.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra Topology
open scoped CGWH.modelCategory

namespace PointedCGWH.modelCategory

private theorem closedTransitions
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), cofibrations PointedCGWH.{u, v} (E.map φ)) :
    ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right) := by
  intro a b φ
  exact PointedCGWH.modelCofibrations_le_closedEmbeddings (E.map φ) (hE φ)

/-- Sources of pointed realized-boundary generators are small with respect to
well-order-continuous chains of selected pointed cofibrations. -/
theorem pointedRealizedBoundarySource_preservesClosedCofibrationColimit
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : PointedCGWH.cofibrantGenerationData.{u, v}.I g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      cofibrations PointedCGWH.{u, v} (E.map φ)) :
    PreservesColimit E (coyoneda.obj (Opposite.op Q)) := by
  change (CGWH.realizedBoundaryInclusions.{u, v}.underCostar CGWH.point) g at hg
  exact PointedCGWH.realizedBoundarySource_preservesClosedColimit g
    (by simpa only [CategoryTheory.MorphismProperty.underCostar] using hg) E
    (closedTransitions E hE)

/-- Sources of pointed realized-horn generators are small with respect to
well-order-continuous chains of selected pointed cofibrations. -/
theorem pointedRealizedHornSource_preservesClosedCofibrationColimit
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : PointedCGWH.cofibrantGenerationData.{u, v}.J g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      cofibrations PointedCGWH.{u, v} (E.map φ)) :
    PreservesColimit E (coyoneda.obj (Opposite.op Q)) := by
  change (CGWH.realizedHornInclusions.{u, v}.underCostar CGWH.point) g at hg
  exact PointedCGWH.realizedHornSource_preservesClosedColimit g
    (by simpa only [CategoryTheory.MorphismProperty.underCostar] using hg) E
    (closedTransitions E hE)

end PointedCGWH.modelCategory
