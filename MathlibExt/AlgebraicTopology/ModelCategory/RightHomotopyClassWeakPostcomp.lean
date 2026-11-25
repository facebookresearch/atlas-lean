/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenRightMateHomotopyClasses

/-!
# Weak postcomposition on actual right homotopy classes

The existing canonical left/right class equivalence transports genuine
model weak postcomposition. Its full map is the existing
postcompOfCofibrant, with the original representative map retained.
-/

noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.RightHomotopyClass

/-- A genuine weak map between fibrant targets gives bijective original right-class postcomposition
from a cofibrant
source. -/
theorem postcompOfCofibrant_bijective_of_weakEquivalence {C : Type u} [Category.{v} C]
    [ModelCategory C]
    {X Y Z : C} [IsCofibrant X] [IsFibrant Y] [IsFibrant Z] (g : Y ⟶ Z) [WeakEquivalence g] :
    Function.Bijective (fun f : RightHomotopyClass X Y => f.postcompOfCofibrant g) := by
  let EY : LeftHomotopyClass X Y ≃ RightHomotopyClass X Y :=
      leftHomotopyClassEquivRightHomotopyClass
  let EZ : LeftHomotopyClass X Z ≃ RightHomotopyClass X Z :=
      leftHomotopyClassEquivRightHomotopyClass
  exact EZ.bijective.comp
      ((LeftHomotopyClass.postcomp_bijective_of_weakEquivalence X g).comp EY.symm.bijective)

end HomotopicalAlgebra.RightHomotopyClass
