/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Linear.Yoneda
public import MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors
public import MathlibExt.AlgebraicGeometry.PDivisibleTangentTests
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Actual formal tangent and cotangent models of a p-divisible group

All tests are actual p-nilpotent R-algebras C with square-zero module M.
Tangent values are the kernel of the actual augmentation map on G(C plus M).
These schemes are affine, so the pointwise level colimit is the p-divisible
sheaf value here. The representing cotangent module is required to be
finite projective and naturally paired with these exact tangent values
on every such algebra/module test; its dual is the formal Lie module.

This models formal Lie over p-complete bases, including O_C, using nilpotent
tests rather than incorrectly differentiating finite torsion groups over a
p-torsionfree base. Scholze--Weinstein1211.6357v2, Sections1-2;
Messing, *Crystals associated to Barsotti-Tate groups*, ChapterII.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleLieModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisiblePointFunctors PDivisibleTangentTests

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  (G : PDivisibleGroup (Spec (.of R)) p)

/-- The actual p-divisible values on all square-zero affine tests. -/
def extensionPoints : Test p R ⥤ CommGrpCat.{0} :=
  (extensionTests p R).rightOp ⋙ pointwisePoints (p := p) (S := Spec (.of R)) G

/-- The actual values after forgetting the nilpotent tangent parameter. -/
def basePoints : Test p R ⥤ CommGrpCat.{0} :=
  (baseTests p R).rightOp ⋙ pointwisePoints (p := p) (S := Spec (.of R)) G

/-- The fixed augmentation map, on the actual geometric point functors. -/
def evaluation : extensionPoints p R G ⟶ basePoints p R G :=
  Functor.whiskerRight (NatTrans.rightOp (augmentations p R))
    (pointwisePoints (p := p) (S := Spec (.of R)) G)

/-- The actual tangent functor, not a freely named Lie carrier. -/
def tangentFunctor : Test p R ⥤ AddCommGrpCat.{0} :=
  kernel (Functor.whiskerRight (evaluation p R G) CommGrpCat.toAddCommGrp)

/-- Restriction of each real test module to the actual base ring. -/
def testModuleFunctor : Test p R ⥤ ModuleCat.{0} R where
  obj C := ModuleCat.of R C.module
  map {C D} f := ModuleCat.ofHom
    { toFun x := f.linear x
      map_add' x y := f.linear.map_add x y
      map_smul' a x := by
        change f.linear (algebraMap R C.algebra a • x) =
          algebraMap R D.algebra a • f.linear x
        rw [f.linear.map_smulₛₗ]
        change f.base (algebraMap R _ a) • f.linear x = _
        rw [f.base.commutes] }
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The prescribed base-module Hom functor on every p-nilpotent test. -/
def cotangentFunctor (W : ModuleCat.{0} R) : Test p R ⥤ AddCommGrpCat.{0} :=
  testModuleFunctor p R ⋙ (linearCoyoneda R (ModuleCat.{0} R)).obj (op W) ⋙
    forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}

/-- A finite-projective representation of the actual formal tangent functor. -/
structure LieModel where
  cotangent : ModuleCat.{0} R
  [finite : Module.Finite R cotangent]
  [projective : Module.Projective R cotangent]
  representation : cotangentFunctor p R cotangent ≅ tangentFunctor p R G

/-- The actual dual cotangent module, with no independent Lie-space choice. -/
abbrev LieModel.lie (L : LieModel p R G) := Module.Dual R L.cotangent

end MathlibExt.AlgebraicGeometry.PDivisibleLieModels
