/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCartesianModel
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Functor objects from a first-projection source

For the actual first-projection/zeroth-row adjunction, the first-projection
source preserves products. Adjoint uniqueness therefore identifies the entire
zeroth row of its Cartesian power with the ordinary simplicial-set functor
object. The comparison retains the actual product maps and both adjunctions;
it does not assert that zeroth-row restriction preserves arbitrary powers.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace.FirstProjection

/-- The same actual first-projection source with the scalar carrier unwrapped. -/
abbrev left : SSet.{u} ⥤ SimplicialSpace.{u} := JoyalSSet.ofSSet ⋙ comparisonLeft

/-- The same actual first-JT right image on its underlying scalar simplicial set. -/
abbrev right : SimplicialSpace.{u} ⥤ SSet.{u} := comparisonRight ⋙ JoyalSSet.forget

/-- The original first-JT adjunction transported only through the scalar carrier equivalence. -/
def adjunction : left.{u} ⊣ right.{u} :=
  JoyalSSet.equivalenceSSet.symm.toAdjunction.comp comparisonAdjunction

private local instance left_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) left.{u} := by
  dsimp [left, comparisonLeft, SSet.simplicialSpaceDiscrete]
  infer_instance

private def compositePowerAdjunction (Q : SSet.{u}) :
    left ⋙ tensorLeft (left.obj Q) ⊣ ihom (left.obj Q) ⋙ right :=
  adjunction.comp (ihom.adjunction (left.obj Q))

private def scalarPowerAdjunction (Q : SSet.{u}) :
    left ⋙ tensorLeft (left.obj Q) ⊣ right ⋙ ihom Q :=
  ((ihom.adjunction Q).comp adjunction).ofNatIsoLeft
    (CartesianMonoidalCategory.prodComparisonNatIso left Q)

/-- The full first-JT right image of a first-projection-source power is the scalar functor object. -/
def functorObjectIso (Q : SSet.{u}) :
    ihom (left.obj Q) ⋙ right ≅ right ⋙ ihom Q :=
  (compositePowerAdjunction Q).rightAdjointUniq (scalarPowerAdjunction Q)

/-- Every scalar test source retains both actual transposes under this entire functor-object Iso. -/
theorem functorObjectIso_transpose (Q P : SSet.{u}) (W : SimplicialSpace.{u})
    (f : left.obj P ⊗ left.obj Q ⟶ W) :
    (compositePowerAdjunction Q).homEquiv P W
        ((β_ (left.obj Q) (left.obj P)).hom ≫ f) ≫ (functorObjectIso Q).hom.app W =
      (scalarPowerAdjunction Q).homEquiv P W
        ((β_ (left.obj Q) (left.obj P)).hom ≫ f) := by
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc,
    (functorObjectIso Q).hom.naturality, ← Category.assoc]
  have h : (compositePowerAdjunction Q).unit.app P ≫
      (functorObjectIso Q).hom.app ((left ⋙ tensorLeft (left.obj Q)).obj P) =
        (scalarPowerAdjunction Q).unit.app P :=
    Adjunction.unit_rightAdjointUniq_hom_app (compositePowerAdjunction Q) (scalarPowerAdjunction Q) P
  rw [h]

/-- The functor-object comparison retains its exact original counit triangle. -/
theorem functorObjectIso_evaluation (Q : SSet.{u}) (W : SimplicialSpace.{u}) :
    (left ⋙ tensorLeft (left.obj Q)).map ((functorObjectIso Q).hom.app W) ≫
        (scalarPowerAdjunction Q).counit.app W =
      (compositePowerAdjunction Q).counit.app W :=
  Adjunction.rightAdjointUniq_hom_app_counit (compositePowerAdjunction Q)
    (scalarPowerAdjunction Q) W

/-- The full comparison is natural in every actual target map. -/
theorem functorObjectIso_target (Q : SSet.{u}) {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    right.map ((ihom (left.obj Q)).map f) ≫ (functorObjectIso Q).hom.app V =
      (functorObjectIso Q).hom.app W ≫ (ihom Q).map (right.map f) :=
  (functorObjectIso Q).hom.naturality f

end SimplicialSpace.FirstProjection
