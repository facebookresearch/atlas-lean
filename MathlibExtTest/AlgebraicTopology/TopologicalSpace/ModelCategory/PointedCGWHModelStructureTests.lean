/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
import MathlibExt.AlgebraicTopology.ModelCategory.Under
import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Tests for the pointed CGWH model structure

These owners pin the seven-name facade, the sole generic undercategory
instance route, independent universes, selected-scope setup and teardown,
the three right-component morphism classes, and the fibrant and well-pointed
cofibrant object criteria.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace MathlibExtTest.PointedCGWHModelStructureTests

section PublicFacadeWithoutScope

#check PointedCGWH.modelCategory
#check PointedCGWH.cofibration_iff
#check PointedCGWH.fibration_iff
#check PointedCGWH.weakEquivalence_iff
#check PointedCGWH.isFibrant_iff
#check PointedCGWH.isCofibrant_iff
#check PointedCGWH.modelCategory.allObjectsFibrant

#check @PointedCGWH.modelCategory.{u, v}
#check @PointedCGWH.modelCategory.{0, 0}
#check @PointedCGWH.modelCategory.{1, 1}
#check @PointedCGWH.modelCategory.{0, 1}
#check @PointedCGWH.modelCategory.{1, 0}

#check @PointedCGWH.cofibration_iff.{u, v}
#check @PointedCGWH.cofibration_iff.{0, 0}
#check @PointedCGWH.cofibration_iff.{1, 1}
#check @PointedCGWH.cofibration_iff.{0, 1}
#check @PointedCGWH.cofibration_iff.{1, 0}

#check @PointedCGWH.fibration_iff.{u, v}
#check @PointedCGWH.fibration_iff.{0, 0}
#check @PointedCGWH.fibration_iff.{1, 1}
#check @PointedCGWH.fibration_iff.{0, 1}
#check @PointedCGWH.fibration_iff.{1, 0}

#check @PointedCGWH.weakEquivalence_iff.{u, v}
#check @PointedCGWH.weakEquivalence_iff.{0, 0}
#check @PointedCGWH.weakEquivalence_iff.{1, 1}
#check @PointedCGWH.weakEquivalence_iff.{0, 1}
#check @PointedCGWH.weakEquivalence_iff.{1, 0}

#check @PointedCGWH.isFibrant_iff.{u, v}
#check @PointedCGWH.isFibrant_iff.{0, 0}
#check @PointedCGWH.isFibrant_iff.{1, 1}
#check @PointedCGWH.isFibrant_iff.{0, 1}
#check @PointedCGWH.isFibrant_iff.{1, 0}

#check @PointedCGWH.isCofibrant_iff.{u, v}
#check @PointedCGWH.isCofibrant_iff.{0, 0}
#check @PointedCGWH.isCofibrant_iff.{1, 1}
#check @PointedCGWH.isCofibrant_iff.{0, 1}
#check @PointedCGWH.isCofibrant_iff.{1, 0}

#check @PointedCGWH.modelCategory.allObjectsFibrant.{u, v}
#check @PointedCGWH.modelCategory.allObjectsFibrant.{0, 0}
#check @PointedCGWH.modelCategory.allObjectsFibrant.{1, 1}
#check @PointedCGWH.modelCategory.allObjectsFibrant.{0, 1}
#check @PointedCGWH.modelCategory.allObjectsFibrant.{1, 0}

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  trivial

end PublicFacadeWithoutScope

section UnderEquation

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    X.hom ≫ f.right = Y.hom :=
  Under.w f

example {A : CGWH.{u, v}} (b : CGWH.point ⟶ A) (g : A ⟶ A)
    (hg : b ≫ g = b) (hne : g ≠ 𝟙 A) :
    let X : PointedCGWH.{u, v} := Under.mk b
    let f : X ⟶ X := Under.homMk g hg
    f.right = g ∧ X.hom ≫ f.right = X.hom ∧ f ≠ 𝟙 X := by
  dsimp
  refine ⟨rfl, hg, ?_⟩
  intro h
  apply hne
  have hRight := congrArg (fun k => k.right) h
  simpa using hRight

end UnderEquation

section SelectedBaseScope

open scoped CGWH.modelCategory

#synth ModelCategory CGWH.{u, v}
#synth ModelCategory PointedCGWH.{u, v}
#synth ModelCategory CGWH.{0, 0}
#synth ModelCategory PointedCGWH.{0, 0}
#synth ModelCategory CGWH.{1, 1}
#synth ModelCategory PointedCGWH.{1, 1}
#synth ModelCategory CGWH.{0, 1}
#synth ModelCategory PointedCGWH.{0, 1}
#synth ModelCategory CGWH.{1, 0}
#synth ModelCategory PointedCGWH.{1, 0}

example : (inferInstance : ModelCategory PointedCGWH.{u, v}) =
    PointedCGWH.modelCategory := rfl

example : (inferInstance : ModelCategory PointedCGWH.{u, v}) =
    HomotopicalAlgebra.ModelCategory.under CGWH.point := rfl

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    PointedCGWH.pointedToCGWH.map f = f.right := rfl

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : Cofibration f) : Cofibration f.right :=
  (PointedCGWH.cofibration_iff f).mp hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : Cofibration f.right) : Cofibration f :=
  (PointedCGWH.cofibration_iff f).mpr hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : Fibration f) : Fibration f.right :=
  (PointedCGWH.fibration_iff f).mp hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : Fibration f.right) : Fibration f :=
  (PointedCGWH.fibration_iff f).mpr hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : WeakEquivalence f) : WeakEquivalence f.right :=
  (PointedCGWH.weakEquivalence_iff f).mp hf

example {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (hf : WeakEquivalence f.right) : WeakEquivalence f :=
  (PointedCGWH.weakEquivalence_iff f).mpr hf

example (X : PointedCGWH.{u, v}) (hX : IsFibrant X) :
    IsFibrant X.right :=
  (PointedCGWH.isFibrant_iff X).mp hX

example (X : PointedCGWH.{u, v}) (hX : IsFibrant X.right) :
    IsFibrant X :=
  (PointedCGWH.isFibrant_iff X).mpr hX

example (X : PointedCGWH.{u, v}) : IsFibrant X :=
  PointedCGWH.modelCategory.allObjectsFibrant X

example (X : PointedCGWH.{0, 0}) : IsFibrant X :=
  PointedCGWH.modelCategory.allObjectsFibrant X

example (X : PointedCGWH.{1, 1}) : IsFibrant X :=
  PointedCGWH.modelCategory.allObjectsFibrant X

example (X : PointedCGWH.{0, 1}) : IsFibrant X :=
  PointedCGWH.modelCategory.allObjectsFibrant X

example (X : PointedCGWH.{1, 0}) : IsFibrant X :=
  PointedCGWH.modelCategory.allObjectsFibrant X

example (_X : PointedCGWH.{u, v}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

example (X : PointedCGWH.{u, v}) (hX : IsCofibrant X) :
    cofibrations CGWH.{u, v} X.hom :=
  (PointedCGWH.isCofibrant_iff X).mp hX

example (X : PointedCGWH.{u, v})
    (hX : cofibrations CGWH.{u, v} X.hom) : IsCofibrant X :=
  (PointedCGWH.isCofibrant_iff X).mpr hX

example (_X : PointedCGWH.{u, v}) : True := by
  fail_if_success
    have _h : IsCofibrant _X ↔ IsCofibrant _X.right :=
      PointedCGWH.isCofibrant_iff _X
  trivial

end SelectedBaseScope

section GenericInstanceDeletion

open scoped CGWH.modelCategory

attribute [-instance] HomotopicalAlgebra.ModelCategory.under in
example : True := by
  let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  trivial

end GenericInstanceDeletion

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : ModelCategory CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  trivial

end ScopeTeardown

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check PointedCGWH.instModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.modelCategory.instModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.realizedBoundaryInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.realizedHornInclusions

#guard_msgs (error, substring := true) in
#check PointedCGWH.cofibrantGenerationData

#guard_msgs (error, substring := true) in
#check PointedCGWH.adj_isQuillenEquivalence

#guard_msgs (error, substring := true) in
#check PointedCGWH.instIsLeftProper

#guard_msgs (error, substring := true) in
#check PointedCGWH.smashModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.spectraModelCategory

end PrivacyAndNonclaims

#print axioms PointedCGWH.modelCategory
#print axioms PointedCGWH.cofibration_iff
#print axioms PointedCGWH.fibration_iff
#print axioms PointedCGWH.weakEquivalence_iff
#print axioms PointedCGWH.isFibrant_iff
#print axioms PointedCGWH.isCofibrant_iff
#print axioms PointedCGWH.modelCategory.allObjectsFibrant

end MathlibExtTest.PointedCGWHModelStructureTests
