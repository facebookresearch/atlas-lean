/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits Topology

namespace MathlibExtTest.PointedCGWHGeneratorSourceSmallness

/-- The actual colimit witness maps to a Hom colimit witness for an arbitrary
closed chain, with no cofibration or coefficient-object instance. -/
example {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (CGWH.realizedHornInclusions.{u, v}.strictMap
      (Under.costar CGWH.point)) g)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right))
    (c : Cocone E) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op Q)).mapCocone c) := by
  let _ : PreservesColimit E (coyoneda.obj (Opposite.op Q)) :=
    PointedCGWH.realizedHornSource_preservesClosedColimit g hg E hE
  exact isColimitOfPreserves _ hc

#print axioms CGWH.realizedGeneratorSource_preservesClosedColimit
#print axioms PointedCGWH.realizedGeneratorSource_preservesClosedColimit
#print axioms PointedCGWH.realizedBoundarySource_preservesClosedColimit
#print axioms PointedCGWH.realizedHornSource_preservesClosedColimit

end MathlibExtTest.PointedCGWHGeneratorSourceSmallness
