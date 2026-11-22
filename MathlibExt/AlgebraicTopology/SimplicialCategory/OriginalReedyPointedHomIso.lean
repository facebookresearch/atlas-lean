/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedJoyalHomEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyGadgetHomPoint
import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputPoint

/-!
# The full original plain pointed Reedy Hom comparison

Both scalar Hom directions use the same actual canonical pointed
copy/forget equivalence. Every original generated Reedy operator and
both original endpoint maps are retained. Genuine point weakness then
applies to the full original plain pointed Hom and its entire original
input-category nerve.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The exact original plain pointed Reedy diagram retaining the same generated objects and maps. -/
def plainReedyDiagram : CosimplicialObject OriginalPointed.Category.{u} := reedyReplacement ⋙ pointedRawFunctor

/-- Both whole original Hom directions identify copied and plain pointed Reedy diagrams in every scalar degree. -/
def plainReedyHomIso (X : OriginalPointed.Category.{u}) :
    OriginalRawRightMapping.reedyHomFunctor.obj (pointedCopyFunctor.obj X) ≅
      CosimplicialObject.homSpace plainReedyDiagram X :=
  NatIso.ofComponents (fun q => (pointedRawHomEquiv (reedyReplacement.obj q.unop) X).toIso)
    (by
      intro q r θ
      apply ConcreteCategory.hom_ext
      intro g
      apply Under.UnderMorphism.ext
      rfl)

/-- The same complete original plain pointed Reedy Hom has genuine point weakness at every fibrant original gadget. -/
theorem plainReedyHom_point_weak (X : OriginalPointed.FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (CosimplicialObject.homSpace plainReedyDiagram X.obj.obj)) := by
  have h := OriginalRawRightMapping.gadgetReedyHom_point_weak X
  have he : (plainReedyHomIso X.obj.obj).hom ≫ SSet.stdSimplex.isTerminalObj₀.from
      (CosimplicialObject.homSpace plainReedyDiagram X.obj.obj) =
      SSet.stdSimplex.isTerminalObj₀.from (OriginalRawRightMapping.gadgetReedyHom X) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact SSet.realizationWeakEquivalences.of_precomp (plainReedyHomIso X.obj.obj).hom _
    (SSet.realizationWeakEquivalences.of_isIso _) (he.symm ▸ h)

/-- The same full original plain Reedy input-category nerve has genuine point weakness at every fibrant original
gadget. -/
theorem plainReedyInputNerve_point_weak (X : OriginalPointed.FibrantMappingGadgets.{u}) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (CostructuredArrow plainReedyDiagram X.obj.obj))) :=
  CosimplicialObject.homInputNerve_point_weak plainReedyDiagram X.obj.obj (plainReedyHom_point_weak X)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
