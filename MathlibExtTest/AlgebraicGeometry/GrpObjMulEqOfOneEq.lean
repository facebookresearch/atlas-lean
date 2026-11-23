/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GrpObjMulEqOfOneEq

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory AlgebraicGeometry

-- exactSource consumer with the original binders.
example {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced (CategoryTheory.Limits.pullback x x)]
    (G₁ G₂ : GrpObj (Over.mk x)) (h : G₁.one = G₂.one) : G₁.mul = G₂.mul :=
  AlgebraicGeometry.GrpObj.mul_eq_of_one_eq x G₁ G₂ h
