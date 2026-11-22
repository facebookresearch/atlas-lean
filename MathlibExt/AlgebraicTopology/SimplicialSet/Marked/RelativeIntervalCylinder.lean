/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinderExact
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomAdjunction
import MathlibExt.CategoryTheory.Adjunction.CopointedOver

/-!
# The actual source-projection interval cylinder in the original marked slice

The old marked interval cylinder is applied to the same source object,
and its original source projection is composed with the supplied whole
base map. Both endpoint maps therefore remain over that same base, rather
than allowing an arbitrary interval-to-base operator. The original
pointwise interval and marks are unchanged; no model is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The original interval source projection lifts the native marked cylinder functor to the supplied marked slice. -/
def relativeIntervalFunctor (Z : Marked.{u}) : Over Z ⥤ Over Z :=
  Adjunction.copointedOverLeft intervalCylinder.{u}.π Z

/-- The same original marked interval and source projection define the actual fixed-base precylinder. -/
def relativeIntervalCylinder (Z : Marked.{u}) : Precylinder (𝟭 (Over Z)) where
  I := relativeIntervalFunctor Z
  i₀ :=
    { app X := Over.homMk (intervalCylinderEndpoint X.left 0) (by
        change intervalCylinderEndpoint X.left 0 ≫ (prodFst _ _ ≫ X.hom) = X.hom
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ X.hom) (intervalCylinderEndpoint_projection X.left 0)).trans (Category.id_comp _)))
      naturality X Y f := by apply Over.OverMorphism.ext; exact intervalCylinderEndpoint_natural f.left 0 }
  i₁ :=
    { app X := Over.homMk (intervalCylinderEndpoint X.left 1) (by
        change intervalCylinderEndpoint X.left 1 ≫ (prodFst _ _ ≫ X.hom) = X.hom
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ X.hom) (intervalCylinderEndpoint_projection X.left 1)).trans (Category.id_comp _)))
      naturality X Y f := by apply Over.OverMorphism.ext; exact intervalCylinderEndpoint_natural f.left 1 }
  π :=
    { app X := Over.homMk (prodFst X.left (max (Δ[1] : SSet.{u}))) rfl
      naturality X Y f := by apply Over.OverMorphism.ext; apply Hom.ext; rfl }
  i₀_π := by
    apply NatTrans.ext
    funext X
    apply Over.OverMorphism.ext
    exact intervalCylinderEndpoint_projection X.left 0
  i₁_π := by
    apply NatTrans.ext
    funext X
    apply Over.OverMorphism.ext
    exact intervalCylinderEndpoint_projection X.left 1

/-- The complete original relative interval object has exactly the old source-projection base map. -/
@[simp]
theorem relativeIntervalCylinder_obj_hom (Z : Marked.{u}) (X : Over Z) :
    ((relativeIntervalCylinder Z).I.obj X).hom = prodFst X.left (max (Δ[1] : SSet.{u})) ≫ X.hom := rfl

/-- The original interval internal-Hom adjunction preserves the same original-universe colimits in the
  fixed-base slice. -/
theorem relativeIntervalCylinder_preservesColimits (Z : Marked.{u}) :
    PreservesColimitsOfSize.{u, u} (relativeIntervalCylinder Z).I :=
  ((internalHomAdjunction (max (Δ[1] : SSet.{u}))).copointedOver intervalCylinder.π Z).leftAdjoint_preservesColimits

end SSet.Marked
