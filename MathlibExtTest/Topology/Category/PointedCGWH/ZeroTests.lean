/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.PointedCGWH.Zero

/-!
# Tests for the zero object of pointed CGWH spaces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace MathlibExtTest.PointedCGWHZeroTests

#check PointedCGWH.instHasZeroObject
#check PointedCGWH.zero_right
#check PointedCGWH.zero_hom

#synth HasZeroObject PointedCGWH.{u, v}
#synth HasZeroObject PointedCGWH.{0, 0}
#synth HasZeroObject PointedCGWH.{1, 1}
#synth HasZeroObject PointedCGWH.{0, 1}
#synth HasZeroObject PointedCGWH.{1, 0}

example :
    (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}).right =
      CGWH.point.{u, v} :=
  PointedCGWH.zero_right

example :
    (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}).hom =
      𝟙 CGWH.point.{u, v} :=
  PointedCGWH.zero_hom

example : IsInitial (0 : PointedCGWH.{u, v}) :=
  HasZeroObject.zeroIsInitial

example : IsTerminal (0 : PointedCGWH.{u, v}) :=
  HasZeroObject.zeroIsTerminal

example (X : PointedCGWH.{u, v}) (f : (0 : PointedCGWH.{u, v}) ⟶ X) :
    f = HasZeroObject.zeroIsInitial.to X :=
  HasZeroObject.zeroIsInitial.hom_ext _ _

example (X : PointedCGWH.{u, v}) (f : X ⟶ (0 : PointedCGWH.{u, v})) :
    f = HasZeroObject.zeroIsTerminal.from X :=
  HasZeroObject.zeroIsTerminal.hom_ext _ _

example (X : PointedCGWH.{u, v}) :
    (Under.mkIdInitial.to X).right = X.hom :=
  Under.mkIdInitial_to_right X

section ZeroMorphisms

local instance : HasZeroMorphisms PointedCGWH.{u, v} :=
  HasZeroObject.zeroMorphismsOfZeroObject

example (X Y Z : PointedCGWH.{u, v}) (f : X ⟶ Y) :
    f ≫ (0 : Y ⟶ Z) = 0 := by simp

example (X Y Z : PointedCGWH.{u, v}) (f : Y ⟶ Z) :
    (0 : X ⟶ Y) ≫ f = 0 := by simp

example (X Y : PointedCGWH.{u, v}) :
    (0 : X ⟶ Y) = HasZeroObject.zeroIsTerminal.from X ≫
      HasZeroObject.zeroIsInitial.to Y :=
  rfl

end ZeroMorphisms

attribute [-instance] PointedCGWH.instHasZeroObject in
example : HasZeroObject PointedCGWH.{u, v} := by
  fail_if_success infer_instance
  exact PointedCGWH.instHasZeroObject

/-- error: Unknown constant `PointedCGWH.modelCategory` -/
#guard_msgs in
#check PointedCGWH.modelCategory

#print axioms PointedCGWH.instHasZeroObject
#print axioms PointedCGWH.zero_right
#print axioms PointedCGWH.zero_hom

end MathlibExtTest.PointedCGWHZeroTests
