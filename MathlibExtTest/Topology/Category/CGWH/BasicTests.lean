/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.CompactlyGenerated
public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# Tests for the basic CGWH category

The tests cover carrier and probe universes, literal continuous-map
morphisms, the unique composite fullness route, and the
homeomorphism/isomorphism adapters.  They also ensure the basic import does
not provide products, (co)limits, adjunctions, or stronger separation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

namespace MathlibExtTest.Topology.Category.CGWH.BasicTests

section SymbolicCarrier

variable (X : CGWH.{u, v})

example : Type v := X

example : CompactlyGenerated.{u, v} := X.toCompactlyGenerated

example : TopCat.{v} := X.toTop

example : UCompactlyGeneratedSpace.{u} X := inferInstance

example : UWeakHausdorffSpace.{u} X := inferInstance

example : T1Space X := inferInstance

example : True := by
  fail_if_success let _ : T2Space X := inferInstance
  trivial

example :
    (inferInstance : TopologicalSpace X) =
      (inferInstance : TopologicalSpace X.toTop) := rfl

end SymbolicCarrier

section UniverseMatrix

example : CGWH.{0, 0} := CGWH.of (Fin 3)

example : CGWH.{1, 1} := CGWH.of (ULift.{1} (Fin 3))

example : CGWH.{0, 1} := CGWH.of (ULift.{1} (Fin 3))

example : CGWH.{1, 0} := CGWH.of (Fin 3)

example : Inhabited CGWH.{0, 0} := inferInstance

example : Inhabited CGWH.{1, 1} := inferInstance

example : Inhabited CGWH.{0, 1} := inferInstance

example : Inhabited CGWH.{1, 0} := inferInstance

end UniverseMatrix

section LiteralMorphisms

variable {A B C : Type v}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [UCompactlyGeneratedSpace.{u} A]
  [UCompactlyGeneratedSpace.{u} B]
  [UCompactlyGeneratedSpace.{u} C]
  [UWeakHausdorffSpace.{u} A]
  [UWeakHausdorffSpace.{u} B]
  [UWeakHausdorffSpace.{u} C]
  (f : C(A, B)) (g : C(B, C)) (a : A)

example : ConcreteCategory.hom (CGWH.ofHom f) = f := rfl

example : ((CGWH.ofHom f : CGWH.of A ⟶ CGWH.of B) : A → B) = f :=
  rfl

example : CGWH.ofHom f a = f a := rfl

example :
    ConcreteCategory.hom
        ((CGWH.ofHom f : CGWH.of A ⟶ CGWH.of B) ≫ CGWH.ofHom g) =
      g.comp f := rfl

end LiteralMorphisms

section Inclusions

variable {X Y : CGWH.{u, v}} (f : X ⟶ Y)

example : CGWH.cgwhToCompactlyGenerated.{u, v}.Full := inferInstance

example : CGWH.cgwhToCompactlyGenerated.{u, v}.Faithful := inferInstance

example : CGWH.cgwhToTop.{u, v}.Full := inferInstance

example : CGWH.cgwhToTop.{u, v}.Faithful := inferInstance

example :
    ConcreteCategory.hom
        (CGWH.cgwhToCompactlyGenerated.map f) =
      ConcreteCategory.hom f := rfl

example :
    ConcreteCategory.hom (CGWH.cgwhToTop.map f) =
      ConcreteCategory.hom f := rfl

variable (h : CGWH.cgwhToTop.obj X ⟶ CGWH.cgwhToTop.obj Y)

example :
    CGWH.cgwhToTop.map (CGWH.cgwhToTop.preimage h) = h :=
  CGWH.cgwhToTop.map_preimage h

example :
    CGWH.cgwhToTop.preimage h =
      CGWH.fullyFaithfulCgwhToTop.preimage h := by
  apply CGWH.fullyFaithfulCgwhToTop.map_injective
  exact (CGWH.cgwhToTop.map_preimage h).trans
    (CGWH.fullyFaithfulCgwhToTop.map_preimage h).symm

example :
    CGWH.fullyFaithfulCgwhToTop.preimage h =
      CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage
        (CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.preimage h) :=
  rfl

end Inclusions

section Adapters

variable {X Y : CGWH.{u, v}}

example (e : X ≃ₜ Y) :
    CGWH.homeoOfIso (CGWH.isoOfHomeo e) = e := by
  ext x
  rfl

example (e : X ≅ Y) :
    CGWH.isoOfHomeo (CGWH.homeoOfIso e) = e := by
  ext x
  rfl

example (e : X ≃ₜ Y) (x : X) :
    (CGWH.isoOfHomeo e).hom x = e x := rfl

example (e : X ≅ Y) (x : X) :
    CGWH.homeoOfIso e x = e.hom x := rfl

end Adapters

section BasicOnlyNegative

example : True := by
  fail_if_success let _ : HasBinaryProducts CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasLimits CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasColimits CGWH.{u, v} := inferInstance
  fail_if_success let _ : CGWH.cgwhToTop.{u, v}.IsLeftAdjoint := inferInstance
  fail_if_success let _ : CGWH.cgwhToTop.{u, v}.IsRightAdjoint := inferInstance
  trivial

end BasicOnlyNegative

#print axioms CGWH
#print axioms CGWH.toCompactlyGenerated
#print axioms CGWH.is_weakHausdorff
#print axioms CGWH.toTop
#print axioms CGWH.of
#print axioms CGWH.ofHom
#print axioms CGWH.cgwhToCompactlyGenerated
#print axioms CGWH.fullyFaithfulCgwhToCompactlyGenerated
#print axioms CGWH.cgwhToTop
#print axioms CGWH.fullyFaithfulCgwhToTop
#print axioms CGWH.isoOfHomeo
#print axioms CGWH.homeoOfIso
#print axioms CGWH.isoEquivHomeo

end MathlibExtTest.Topology.Category.CGWH.BasicTests
