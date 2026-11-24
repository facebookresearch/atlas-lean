/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Limits.Shapes.Cofiber

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CategoryTheory.Limits.Shapes.CofiberTests

#check @HomotopicalAlgebra.cofiberSpan
#check @HomotopicalAlgebra.ordinaryCofiber

variable {C : Type u} [Category.{v} C]
variable [HasTerminal C] [HasColimitsOfShape WalkingSpan C]

example : Arrow C ⥤ (WalkingSpan ⥤ C) :=
  HomotopicalAlgebra.cofiberSpan

example : Arrow C ⥤ C :=
  HomotopicalAlgebra.ordinaryCofiber

-- The neutral API constructs the unique map from any full caller cofiber cocone.
example (f : Arrow C) {W : C} (q : f.right ⟶ W) (z : (⊤_ C) ⟶ W)
    (h : f.hom ≫ q = terminal.from f.left ≫ z) :
    ∃! k : (HomotopicalAlgebra.ordinaryCofiber (C := C)).obj f ⟶ W,
      HomotopicalAlgebra.ordinaryCofiberTarget f ≫ k = q ∧
        HomotopicalAlgebra.ordinaryCofiberPoint f ≫ k = z := by
  let sq := HomotopicalAlgebra.ordinaryCofiberIsPushout f
  refine ⟨sq.desc q z h, ⟨sq.inl_desc q z h, sq.inr_desc q z h⟩, ?_⟩
  intro k hk
  apply sq.hom_ext
  · exact hk.1.trans (sq.inl_desc q z h).symm
  · exact hk.2.trans (sq.inr_desc q z h).symm

-- Both components of an arbitrary Arrow square act on the same selected cocone.
example {A B A' B' : C} (i : A ⟶ B) (j : A' ⟶ B')
    (p : A ⟶ A') (q : B ⟶ B') (h : p ≫ j = i ≫ q) :
    HomotopicalAlgebra.ordinaryCofiberTarget (Arrow.mk i) ≫
        (HomotopicalAlgebra.ordinaryCofiber (C := C)).map
          (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk j) p q h) =
      q ≫ HomotopicalAlgebra.ordinaryCofiberTarget (Arrow.mk j) ∧
    HomotopicalAlgebra.ordinaryCofiberPoint (Arrow.mk i) ≫
        (HomotopicalAlgebra.ordinaryCofiber (C := C)).map
          (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk j) p q h) =
      HomotopicalAlgebra.ordinaryCofiberPoint (Arrow.mk j) :=
  ⟨HomotopicalAlgebra.ordinaryCofiberTarget_naturality
      (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk j) p q h),
    HomotopicalAlgebra.ordinaryCofiberPoint_naturality
      (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk j) p q h)⟩

/-- error: Unknown identifier `HomotopicalAlgebra.homotopyCofiber` -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.homotopyCofiber

#print axioms HomotopicalAlgebra.cofiberSpan
#print axioms HomotopicalAlgebra.ordinaryCofiber
#print axioms HomotopicalAlgebra.ordinaryCofiberTarget
#print axioms HomotopicalAlgebra.ordinaryCofiberPoint
#print axioms HomotopicalAlgebra.ordinaryCofiberIsPushout
#print axioms HomotopicalAlgebra.ordinaryCofiberTarget_naturality
#print axioms HomotopicalAlgebra.ordinaryCofiberPoint_naturality

end MathlibExtTest.CategoryTheory.Limits.Shapes.CofiberTests
