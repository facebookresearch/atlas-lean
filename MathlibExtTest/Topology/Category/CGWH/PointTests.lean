/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Point

/-!
# Tests for the CGWH point object
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

namespace MathlibExtTest.Topology.Category.CGWH.PointTests

#check @CGWH.point
#check @CGWH.point_isTerminal
#check CGWH.pointHomEquiv
#check CGWH.pointHomEquiv_apply
#check CGWH.pointHomEquiv_symm_apply_apply

example : (CGWH.point.{u, v} : Type v) = PUnit.{v + 1} := rfl

example : UCompactlyGeneratedSpace.{u} CGWH.point.{u, v} := inferInstance

example : UWeakHausdorffSpace.{u} CGWH.point.{u, v} := inferInstance

example : T1Space CGWH.point.{u, v} := inferInstance

example : CGWH.{0, 0} := CGWH.point

example : CGWH.{1, 1} := CGWH.point

example : CGWH.{0, 1} := CGWH.point

example : CGWH.{1, 0} := CGWH.point

section Terminal

variable (X : CGWH.{u, v}) (x : X)

example : CGWH.point_isTerminal.from X x = PUnit.unit := rfl

example
    (f : X ⟶ CGWH.point.{u, v}) :
    f = CGWH.point_isTerminal.from X :=
  CGWH.point_isTerminal.hom_ext _ _

end Terminal

section Evaluation

variable (X : CGWH.{u, v}) (x : X)

example : (CGWH.point.{u, v} ⟶ X) ≃ X :=
  CGWH.pointHomEquiv X

example : CGWH.pointHomEquiv X ((CGWH.pointHomEquiv X).symm x) = x :=
  (CGWH.pointHomEquiv X).apply_symm_apply x

end Evaluation

section NoChosenStructure

example : True := by
  fail_if_success let _ : HasTerminal CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasBinaryProducts CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasBinaryCoproducts CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasLimits CGWH.{u, v} := inferInstance
  fail_if_success let _ : HasColimits CGWH.{u, v} := inferInstance
  trivial

end NoChosenStructure

#print axioms CGWH.point
#print axioms CGWH.point_isTerminal
#print axioms CGWH.pointHomEquiv

end MathlibExtTest.Topology.Category.CGWH.PointTests
