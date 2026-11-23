/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Tests for basic pointed CGWH spaces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.Limits

namespace MathlibExtTest.Topology.Category.PointedCGWH.BasicTests

#check PointedCGWH
#check @PointedCGWH.pointedToCGWH

example : PointedCGWH.{u, v} = Under CGWH.point.{u, v} := rfl

example : PointedCGWH.{0, 0} = Under CGWH.point.{0, 0} := rfl

example : PointedCGWH.{1, 1} = Under CGWH.point.{1, 1} := rfl

example : PointedCGWH.{0, 1} = Under CGWH.point.{0, 1} := rfl

example : PointedCGWH.{1, 0} = Under CGWH.point.{1, 0} := rfl

section ObjectsAndMorphisms

variable {X Y Z : CGWH.{u, v}}
  (bX : CGWH.point ⟶ X) (bY : CGWH.point ⟶ Y)
  (bZ : CGWH.point ⟶ Z)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  (hf : bX ≫ f = bY) (hg : bY ≫ g = bZ)

example : PointedCGWH.{u, v} := Under.mk bX

example : (Under.mk bX : PointedCGWH.{u, v}).right = X := rfl

example : (Under.mk bX : PointedCGWH.{u, v}).hom = bX := rfl

example : Under.mk bX ⟶ Under.mk bY :=
  Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf

example :
    (Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf).right = f :=
  rfl

example :
    (Under.mk bX).hom ≫
        (Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf).right =
      (Under.mk bY).hom :=
  Under.w (Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf)

example :
    Under.Hom.right (𝟙 (Under.mk bX : PointedCGWH.{u, v})) = 𝟙 X :=
  Under.id_right (Under.mk bX)

example :
    (Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf ≫
        Under.homMk (U := Under.mk bY) (V := Under.mk bZ) g hg).right =
      f ≫ g :=
  Under.comp_right _ _ _ _ _

example : PointedCGWH.pointedToCGWH.obj (Under.mk bX) = X := rfl

example :
    PointedCGWH.pointedToCGWH.map
        (Under.homMk (U := Under.mk bX) (V := Under.mk bY) f hf) = f :=
  Under.forget_map

end ObjectsAndMorphisms

section NoFurtherStructure

example : True := by
  fail_if_success let _ : HasBinaryCoproducts CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasLimits PointedCGWH.{u, v} := inferInstance
  fail_if_success let _ : HasColimits PointedCGWH.{u, v} := inferInstance
  trivial

end NoFurtherStructure

/-- error: Unknown constant `PointedCGWH.addBasepoint` -/
#guard_msgs in
#check PointedCGWH.addBasepoint

#print axioms PointedCGWH
#print axioms PointedCGWH.pointedToCGWH

end MathlibExtTest.Topology.Category.PointedCGWH.BasicTests
