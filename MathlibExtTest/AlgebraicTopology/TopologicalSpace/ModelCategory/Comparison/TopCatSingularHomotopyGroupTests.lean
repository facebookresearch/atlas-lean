/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup

/-!
# Tests for cube-to-singular homotopy groups

The matrix checks every public declaration in symbolic, zero, and one
universes, including degrees one and two, equality-aware naturality,
source-first composition, and the noncommutative basepoint conjugation law.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Simplicial
open scoped Simplicial Topology

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison
namespace TopCatSingularHomotopyGroupTests

section Comparison

variable {X Y Z : TopCat.{u}} (n : ℕ)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  {x : X} {y : Y} {z : Z}
  (hf : f x = y) (hg : g y = z)
  (hfg : (g.hom.comp f.hom) x = z)
  (a : HomotopyGroup.Pi (n + 1) X x)

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi (n + 1) X x ≃*
      SSet.KanComplex.π (n + 1) K
        (TopCat.toSSetObj₀Equiv.symm x) :=
  TopCat.homotopyGroupSingularMulEquiv n X x

example :
    let KX := TopCat.toSSet.obj X
    let KY := TopCat.toSSet.obj Y
    let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
    let hs : (TopCat.toSSet.map f).app _
        (TopCat.toSSetObj₀Equiv.symm x) =
        TopCat.toSSetObj₀Equiv.symm y := by
      exact congrArg (TopCat.toSSetObj₀Equiv (X := Y)).symm hf
    TopCat.homotopyGroupSingularMulEquiv n Y y
        (HomotopyGroup.mapHomOfEq f.hom hf n a) =
      SSet.KanComplex.π.map (TopCat.toSSet.map f) hs (n + 1)
        (TopCat.homotopyGroupSingularMulEquiv n X x a) :=
  TopCat.homotopyGroupSingularMulEquiv_naturality n f hf a

example :
    let K := TopCat.toSSet.obj X
    let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    TopCat.homotopyGroupSingularMulEquiv n X x
        (HomotopyGroup.mapHomOfEq (ContinuousMap.id X) rfl n a) =
      SSet.KanComplex.π.map (TopCat.toSSet.map (𝟙 X)) rfl (n + 1)
        (TopCat.homotopyGroupSingularMulEquiv n X x a) :=
  TopCat.homotopyGroupSingularMulEquiv_id n X x a

example :
    let KX := TopCat.toSSet.obj X
    let KZ := TopCat.toSSet.obj Z
    let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex KZ := TopCat.toSSet_obj_kanComplex Z
    let hsfg : (TopCat.toSSet.map f ≫ TopCat.toSSet.map g).app _
        (TopCat.toSSetObj₀Equiv.symm x) =
        TopCat.toSSetObj₀Equiv.symm z := by
      exact congrArg (TopCat.toSSetObj₀Equiv (X := Z)).symm hfg
    TopCat.homotopyGroupSingularMulEquiv n Z z
        (HomotopyGroup.mapHomOfEq (g.hom.comp f.hom) hfg n a) =
      SSet.KanComplex.π.map
        (TopCat.toSSet.map f ≫ TopCat.toSSet.map g) hsfg (n + 1)
        (TopCat.homotopyGroupSingularMulEquiv n X x a) :=
  TopCat.homotopyGroupSingularMulEquiv_comp
    n f g hf hg hfg a

end Comparison

section DegreeOne

variable (X : TopCat.{u}) (x : X)
  (a : HomotopyGroup.Pi 1 X x)

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    TopCat.singularFundamentalGroupoidEndMulEquiv X x
      (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
        (TopCat.toSSetObj₀Equiv.symm x)
        (TopCat.homotopyGroupSingularMulEquiv 0 X x a)) =
      HomotopyGroup.pi1MulEquivFundamentalGroup a :=
  TopCat.homotopyGroupSingularMulEquiv_piOne X x a

end DegreeOne

section BasepointChange

variable {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y)
  {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z)
  (a : HomotopyGroup.Pi (n + 1) X x)

example :
    HomotopyGroup.Pi (n + 1) X x ≃*
      HomotopyGroup.Pi (n + 1) X y :=
  TopCat.homotopyGroupBasepointChangeMulEquiv n X p

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    TopCat.homotopyGroupSingularMulEquiv n X y
        (TopCat.homotopyGroupBasepointChangeMulEquiv n X p a) =
      SSet.KanComplex.π.action (TopCat.singularPathHom X p)
        (TopCat.homotopyGroupSingularMulEquiv n X x a) :=
  TopCat.homotopyGroupSingularMulEquiv_basepointChange n X p a

example :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X
        (_root_.Path.refl x) =
      MulEquiv.refl (HomotopyGroup.Pi (n + 1) X x) :=
  TopCat.homotopyGroupBasepointChangeMulEquiv_refl n X x

example :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X (p.trans q) =
      (TopCat.homotopyGroupBasepointChangeMulEquiv n X p).trans
        (TopCat.homotopyGroupBasepointChangeMulEquiv n X q) :=
  TopCat.homotopyGroupBasepointChangeMulEquiv_trans n X p q

example :
    HomotopyGroup.map f.hom
        (TopCat.homotopyGroupBasepointChangeMulEquiv n X p a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n Y
        (p.map f.hom.continuous) (HomotopyGroup.map f.hom a) :=
  TopCat.homotopyGroupBasepointChangeMulEquiv_naturality n f p a

example (b : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
        (TopCat.homotopyGroupBasepointChangeMulEquiv 0 X p b) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (HomotopyGroup.pi1MulEquivFundamentalGroup b) :=
  TopCat.homotopyGroupBasepointChangeMulEquiv_piOne X p b

end BasepointChange

section DegreeMatrix

variable (X : TopCat.{u}) (x : X)

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi 1 X x ≃*
      SSet.KanComplex.π 1 K (TopCat.toSSetObj₀Equiv.symm x) :=
  TopCat.homotopyGroupSingularMulEquiv 0 X x

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi 2 X x ≃*
      SSet.KanComplex.π 2 K (TopCat.toSSetObj₀Equiv.symm x) :=
  TopCat.homotopyGroupSingularMulEquiv 1 X x

end DegreeMatrix

section UniverseZero

variable (X : TopCat.{0}) (x : X)

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi 1 X x ≃*
      SSet.KanComplex.π 1 K (TopCat.toSSetObj₀Equiv.symm x) :=
  TopCat.homotopyGroupSingularMulEquiv 0 X x

end UniverseZero

section UniverseOne

variable (X : TopCat.{1}) (x : X)

example :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi 2 X x ≃*
      SSet.KanComplex.π 2 K (TopCat.toSSetObj₀Equiv.symm x) :=
  TopCat.homotopyGroupSingularMulEquiv 1 X x

end UniverseOne

#print axioms TopCat.homotopyGroupSingularMulEquiv
#print axioms TopCat.homotopyGroupSingularMulEquiv_naturality
#print axioms TopCat.homotopyGroupSingularMulEquiv_id
#print axioms TopCat.homotopyGroupSingularMulEquiv_comp
#print axioms TopCat.homotopyGroupSingularMulEquiv_piOne
#print axioms TopCat.homotopyGroupBasepointChangeMulEquiv
#print axioms TopCat.homotopyGroupSingularMulEquiv_basepointChange
#print axioms TopCat.homotopyGroupBasepointChangeMulEquiv_refl
#print axioms TopCat.homotopyGroupBasepointChangeMulEquiv_trans
#print axioms TopCat.homotopyGroupBasepointChangeMulEquiv_naturality
#print axioms TopCat.homotopyGroupBasepointChangeMulEquiv_piOne

end TopCatSingularHomotopyGroupTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison
