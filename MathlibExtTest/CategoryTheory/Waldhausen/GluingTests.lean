/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.Gluing

/-!
# Tests for the explicit Waldhausen gluing carrier

These clients pin the two pushout rows, both distinguished cofibrations, the
four comparison maps, and the three weak span components.  The carrier is an
explicit proposition, not an inferred typeclass, and no inherited arrow
gluing statement is claimed.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace GluingTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

section SymbolicCube

variable (hGlue : WaldhausenGluingAxiom (C := C))
variable {X Y Z P X' Y' Z' P' : C}
variable {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
variable {i' : X' ⟶ Y'} {f' : X' ⟶ Z'}
  {inY' : Y' ⟶ P'} {inZ' : Z' ⟶ P'}
variable (hP : IsPushout i f inY inZ)
  (hP' : IsPushout i' f' inY' inZ')
variable (x : X ⟶ X') (y : Y ⟶ Y') (z : Z ⟶ Z') (p : P ⟶ P')
variable (hi : IsCofibration i) (hi' : IsCofibration i')
variable (hiy : i ≫ y = x ≫ i') (hfz : f ≫ z = x ≫ f')
variable (hY : inY ≫ p = y ≫ inY') (hZ : inZ ≫ p = z ≫ inZ')
variable (hx : IsWeakEquivalence x) (hy : IsWeakEquivalence y)
  (hz : IsWeakEquivalence z)

example : IsWeakEquivalence p :=
  hGlue.gluing hP hP' x y z p hi hi' hiy hfz hY hZ hx hy hz

end SymbolicCube

section IdentityCube

variable (hGlue : WaldhausenGluingAxiom (C := C))
variable {X Y Z P : C} {i : X ⟶ Y} {f : X ⟶ Z}
  {inY : Y ⟶ P} {inZ : Z ⟶ P}
variable (hP : IsPushout i f inY inZ) (hi : IsCofibration i)

example : IsWeakEquivalence (𝟙 P) := by
  apply hGlue.gluing hP hP (𝟙 X) (𝟙 Y) (𝟙 Z) (𝟙 P) hi hi
  · simp
  · simp
  · simp
  · simp
  · exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).id_mem X
  · exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).id_mem Y
  · exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).id_mem Z

end IdentityCube

#guard_msgs (error, substring := true) in
#synth WaldhausenGluingAxiom (C := C)

#guard_msgs (error, substring := true) in
#check CategoryTheory.arrowGluingAxiom

#guard_msgs (error, substring := true) in
#check CategoryTheory.cofibrationArrowGluingAxiom

#guard_msgs (error, substring := true) in
#check CategoryTheory.WaldhausenGluingAxiom.of_hasTwoOutOfThree

#print axioms CategoryTheory.WaldhausenGluingAxiom
#print axioms CategoryTheory.WaldhausenGluingAxiom.gluing

end GluingTests
end MathlibExtTest.CategoryTheory.Waldhausen
