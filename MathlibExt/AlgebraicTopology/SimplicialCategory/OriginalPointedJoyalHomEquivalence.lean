/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontJoyalPointedDiagram

/-!
# Full original pointed Hom equivalence across the named Joyal carrier

The canonical copy and forget functors give both full Hom directions
for arbitrary original pointed objects, including the actual generated
Reedy degrees. Every underlying original simplex map and boundary
triangle is retained; object and Hom levels are the original ones.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same original full Hom and its canonical Joyal-tagged Hom have both actual inverse maps. -/
def pointedHomCopyEquiv (X Y : Under (∂Δ[1] : SSet.{u})) :
    (X ⟶ Y) ≃ (pointedCopyFunctor.obj X ⟶ pointedCopyFunctor.obj Y) where
  toFun := pointedCopyFunctor.map
  invFun := pointedRawFunctor.map
  left_inv f := by apply Under.UnderMorphism.ext; rfl
  right_inv f := by apply Under.UnderMorphism.ext; apply JoyalSSet.homEquiv.injective; rfl

/-- The same full original Hom from a named Joyal object to a copied pointed target retains both underlying
directions. -/
def pointedRawHomEquiv (X : PointedJoyal.{u}) (Y : Under (∂Δ[1] : SSet.{u})) :
    (X ⟶ pointedCopyFunctor.obj Y) ≃ (pointedRawFunctor.obj X ⟶ Y) where
  toFun := pointedRawFunctor.map
  invFun := pointedCopyFunctor.map
  left_inv f := by apply Under.UnderMorphism.ext; apply JoyalSSet.homEquiv.injective; rfl
  right_inv f := by apply Under.UnderMorphism.ext; rfl

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
