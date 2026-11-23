/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.ClassifyingSpace.CGWHWeakHSpace
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Category.ULift

/-!
# Categorical CGWH weak H-space tests

Consumers for the generic construction, a genuinely non-strict categorical
unit, identity natural transformations, and a raised-universe boundary.
-/

open CategoryTheory

universe w u

namespace MathlibExtTest.CategoryTheory.ClassifyingSpace
namespace CGWHWeakHSpaceTests

noncomputable section

section Generic

variable (D : Type u) [Category.{u} D]
variable (mu : D × D ⥤ D) (e : D)
variable (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D)
variable (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D)
variable (unit_app_eq : leftUnit.hom.app e = rightUnit.hom.app e)

example :
    CGWH.WeakHSpaceData
      (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D)) :=
  categoricalClassifyingSpaceWeakHSpaceData.{w}
    D mu e leftUnit rightUnit unit_app_eq

example :
    Path
      (categoricalClassifyingSpaceMul.{w} D mu
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint.{w} e)
          (classifyingSpaceCGWHPoint.{w} e)))
      (classifyingSpaceCGWHPoint.{w} e) :=
  categoricalClassifyingSpaceRootPath.{w} D mu e leftUnit

example :
    CGWH.hspaceLeftUnitMap
        (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e) =
      classifyingSpaceCGWH.{w, u, u}.map
        (categoricalLeftUnitFunctor D mu e).toCatHom :=
  categoricalClassifyingSpaceMul_leftUnitMap.{w} D mu e

example :
    CGWH.hspaceRightUnitMap
        (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e) =
      classifyingSpaceCGWH.{w, u, u}.map
        (categoricalRightUnitFunctor D mu e).toCatHom :=
  categoricalClassifyingSpaceMul_rightUnitMap.{w} D mu e

example (x y : D) :
    categoricalClassifyingSpaceMul.{w} D mu
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint.{w} x)
          (classifyingSpaceCGWHPoint.{w} y)) =
      classifyingSpaceCGWHPoint.{w} (mu.obj (x, y)) := by
  simp

example (p q : FundamentalGroup
    (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D))
    (classifyingSpaceCGWHPoint.{w} e)) :
    p * q = q * p :=
  categoricalClassifyingSpace_fundamentalGroup_mul_comm.{w}
    D mu e leftUnit rightUnit unit_app_eq p q

/-- The order pins the reversed path-concatenation convention inherited by
the fundamental group. -/
example (a b c d : FundamentalGroup
    (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D))
    (classifyingSpaceCGWHPoint.{w} e)) :
    (categoricalClassifyingSpaceWeakHSpaceData.{w}
      D mu e leftUnit rightUnit unit_app_eq).fundamentalMul
        (a * b) (c * d) =
      (categoricalClassifyingSpaceWeakHSpaceData.{w}
        D mu e leftUnit rightUnit unit_app_eq).fundamentalMul a c *
      (categoricalClassifyingSpaceWeakHSpaceData.{w}
        D mu e leftUnit rightUnit unit_app_eq).fundamentalMul b d :=
  (categoricalClassifyingSpaceWeakHSpaceData.{w}
    D mu e leftUnit rightUnit unit_app_eq).fundamentalMul_interchange
      a b c d

example : True := by
  fail_if_success
    let _ := inferInstanceAs (CommGroup (FundamentalGroup
      (classifyingSpaceCGWH.{w, u, u}.obj (Cat.of D))
      (classifyingSpaceCGWHPoint.{w} e)))
  trivial

end Generic

section NonStrictUnit

abbrev TestCategory := Codiscrete Bool

def testUnit : TestCategory := Codiscrete.mk false

def testProductObject : TestCategory := Codiscrete.mk true

def testMul : TestCategory × TestCategory ⥤ TestCategory :=
  (Functor.const (TestCategory × TestCategory)).obj testProductObject

def testLeftUnit :
    categoricalLeftUnitFunctor TestCategory testMul testUnit ≅
      𝟭 TestCategory :=
  Codiscrete.natIso

def testRightUnit :
    categoricalRightUnitFunctor TestCategory testMul testUnit ≅
      𝟭 TestCategory :=
  Codiscrete.natIso

theorem testUnit_app_eq :
    testLeftUnit.hom.app testUnit = testRightUnit.hom.app testUnit :=
  Subsingleton.elim _ _

/-- This fixture genuinely does not have a strict object-level unit. -/
example : testMul.obj (testUnit, testUnit) ≠ testUnit := by
  intro h
  have := congrArg Codiscrete.as h
  contradiction

example :
    CGWH.WeakHSpaceData
      (classifyingSpaceCGWH.{0, 0, 0}.obj (Cat.of TestCategory)) :=
  categoricalClassifyingSpaceWeakHSpaceData
    TestCategory testMul testUnit testLeftUnit testRightUnit testUnit_app_eq

example :
    categoricalClassifyingSpaceMul TestCategory testMul
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint testUnit)
          (classifyingSpaceCGWHPoint testUnit)) =
      classifyingSpaceCGWHPoint testProductObject := by
  rw [categoricalClassifyingSpaceMul_prodPoint]
  rfl

example :
    categoricalClassifyingSpaceRootPath
        TestCategory testMul testUnit testLeftUnit 0 =
      categoricalClassifyingSpaceMul TestCategory testMul
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint testUnit)
          (classifyingSpaceCGWHPoint testUnit)) :=
  (categoricalClassifyingSpaceRootPath
    TestCategory testMul testUnit testLeftUnit).source

example :
    categoricalClassifyingSpaceRootPath
        TestCategory testMul testUnit testLeftUnit 1 =
      classifyingSpaceCGWHPoint testUnit :=
  (categoricalClassifyingSpaceRootPath
    TestCategory testMul testUnit testLeftUnit).target

example :
    CGWH.hspaceLeftUnitPath _ _ _
        (categoricalClassifyingSpaceLeftUnitHomotopy
          TestCategory testMul testUnit testLeftUnit) =
      categoricalClassifyingSpaceRootPath
        TestCategory testMul testUnit testLeftUnit :=
  categoricalClassifyingSpaceLeftUnitPath_eq_rootPath
    TestCategory testMul testUnit testLeftUnit

example :
    CGWH.hspaceRightUnitPath _ _ _
        (categoricalClassifyingSpaceRightUnitHomotopy
          TestCategory testMul testUnit testRightUnit) =
      categoricalClassifyingSpaceRootPath
        TestCategory testMul testUnit testLeftUnit :=
  categoricalClassifyingSpaceRightUnitPath_eq_rootPath
    TestCategory testMul testUnit testLeftUnit testRightUnit testUnit_app_eq

end NonStrictUnit

section IdentityBoundary

variable (D : Type u) [Category.{u} D] (d : D)

example :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, u, u}.map (𝟙 (Cat.of D)))).hom
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, u, u}.map (𝟙 (Cat.of D)))).hom :=
  classifyingSpaceCGWHNatTransHomotopy.{w} (𝟙 (𝟭 D))

example :
    (classifyingSpaceCGWHNatTransHomotopy.{w} (𝟙 (𝟭 D))).evalAt
        (classifyingSpaceCGWHPoint.{w} d) =
      ((TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (𝟙 d)))).map
            (classifyingSpaceCGWHToTopIso.{w, u, u}.app
              (Cat.of D)).inv.hom.continuous).cast
        ((classifyingSpaceCGWH_map_point.{w} (𝟭 D) d).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex d))
        ((classifyingSpaceCGWH_map_point.{w} (𝟭 D) d).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex d)) :=
  classifyingSpaceCGWHNatTransHomotopy_evalAt.{w} (𝟙 (𝟭 D)) d

end IdentityBoundary

section RaisedUniverse

variable (D : Type 1) [Category.{1} D]
variable (mu : D × D ⥤ D) (e : D)
variable (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D)
variable (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D)
variable (unit_app_eq : leftUnit.hom.app e = rightUnit.hom.app e)

example :
    CGWH.WeakHSpaceData
      (classifyingSpaceCGWH.{1, 1, 1}.obj (Cat.of D)) :=
  categoricalClassifyingSpaceWeakHSpaceData.{1}
    D mu e leftUnit rightUnit unit_app_eq

example (p q : FundamentalGroup
    (classifyingSpaceCGWH.{1, 1, 1}.obj (Cat.of D))
    (classifyingSpaceCGWHPoint.{1} e)) :
    p * q = q * p :=
  categoricalClassifyingSpace_fundamentalGroup_mul_comm.{1}
    D mu e leftUnit rightUnit unit_app_eq p q

end RaisedUniverse

#print axioms categoricalLeftUnitFunctor
#print axioms categoricalRightUnitFunctor
#print axioms categoricalClassifyingSpaceMul
#print axioms categoricalClassifyingSpaceMul_prodPoint
#print axioms nerveMap_constFunctor
#print axioms classifyingSpaceCGWH_map_constFunctor
#print axioms classifyingSpaceCGWH_prodLift
#print axioms categoricalClassifyingSpaceMul_leftUnitMap
#print axioms categoricalClassifyingSpaceMul_rightUnitMap
#print axioms classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex
#print axioms classifyingSpaceCGWHNatTransHomotopy
#print axioms classifyingSpaceCGWHNatTransHomotopy_evalAt
#print axioms categoricalClassifyingSpaceRootPath
#print axioms categoricalClassifyingSpaceLeftUnitHomotopy
#print axioms categoricalClassifyingSpaceRightUnitHomotopy
#print axioms categoricalClassifyingSpaceLeftUnitPath_eq_rootPath
#print axioms categoricalClassifyingSpaceRightUnitPath_eq_rootPath
#print axioms categoricalClassifyingSpaceWeakHSpaceData
#print axioms categoricalClassifyingSpace_fundamentalGroup_mul_comm

end

end CGWHWeakHSpaceTests
end MathlibExtTest.CategoryTheory.ClassifyingSpace
