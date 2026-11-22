/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedRightMappingFunctor

/-!
# Whole original source naturality of the actual Reedy mapping comparison

Every original pointed source arrow postcomposes the full same Hom
simplices. Restriction along the generated original Reedy map commutes
with that postcomposition in all scalar degrees and preserves the same
original endpoint quotient readbacks.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

/-- The full original pointed Joyal Hom diagram with a variable same original target. -/
def reedyHomFunctor : PointedJoyal.{u} ⥤ SSet.{u} :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj reedyReplacement.op

/-- The full original fixed-front Hom diagram with a variable same original target. -/
def fixedFrontHomFunctor : PointedJoyal.{u} ⥤ SSet.{u} :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj pointedJoyalDiagram.op

/-- The same generated original Reedy map is a whole natural comparison at every pointed target. -/
def reedyHomTransformation : reedyHomFunctor.{u} ⟶ fixedFrontHomFunctor.{u} where
  app X :=
    (Functor.isoWhiskerLeft reversedFactorization.Z (Coyoneda.objOpOp X)).inv ≫
      Functor.whiskerRight reversedFactorization.p (coyoneda.obj (op (op X))) ≫
        (Functor.isoWhiskerLeft pointedJoyalDiagram.op (Coyoneda.objOpOp X)).hom
  naturality X Y f := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro g
    apply Under.UnderMorphism.ext
    change (reedyReplacementMap.app q.unop ≫ (g ≫ f)).right =
      ((reedyReplacementMap.app q.unop ≫ g) ≫ f).right
    exact congrArg Under.Hom.right (Category.assoc (reedyReplacementMap.app q.unop) g f).symm

/-- The entire original target-dependent comparison specializes to the same actual original mapping comparison. -/
theorem reedyHomTransformation_app {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K) :
    reedyHomTransformation.app (pointedCopyFunctor.obj (pointedInput a b)) = reedyHomComparison a b := rfl

/-- Every full original target-map naturality square retains the same generated restriction and entire
postcomposition. -/
theorem reedyHomTransformation_naturality {X Y : PointedJoyal.{u}} (f : X ⟶ Y) :
    reedyHomFunctor.map f ≫ reedyHomTransformation.app Y =
      reedyHomTransformation.app X ≫ fixedFrontHomFunctor.map f :=
  reedyHomTransformation.naturality f

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
