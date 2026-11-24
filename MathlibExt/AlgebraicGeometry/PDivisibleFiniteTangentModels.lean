/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleLieModels

/-!
# Actual finite-level tangent maps into the formal p-divisible tangent

Every finite tangent is the kernel of the original group-scheme
augmentation on the entire square-zero test category. The inclusion
into the formal tangent is the native map of these kernels, induced by
the original finite point inclusion. This is the normalization used
for finite-to-formal Cartier cotangent/Hodge--Tate comparison.

Sources: Messing, The crystals associated to Barsotti--Tate groups,
Chapter II; Scholze--Weinstein, arXiv:1211.6357v2, Sections 1--3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleFiniteTangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisiblePointFunctors PDivisibleTangentTests

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  (G : PDivisibleGroup (Spec (.of R)) p)

/-- Original finite-level points on every actual square-zero extension. -/
def extensionPoints (n : ℕ) : Test p R ⥤ AddCommGrpCat.{0} :=
  (extensionTests p R).rightOp ⋙ levelPoints (p := p) (S := Spec (.of R)) G n ⋙
    CommGrpCat.toAddCommGrp

/-- Original finite-level points after forgetting the nilpotent tangent module. -/
def basePoints (n : ℕ) : Test p R ⥤ AddCommGrpCat.{0} :=
  (baseTests p R).rightOp ⋙ levelPoints (p := p) (S := Spec (.of R)) G n ⋙
    CommGrpCat.toAddCommGrp

/-- The original finite group augmentation, on this full test category. -/
def evaluation (n : ℕ) : extensionPoints p R G n ⟶ basePoints p R G n :=
  Functor.whiskerRight (NatTrans.rightOp (augmentations p R))
    (levelPoints (p := p) (S := Spec (.of R)) G n ⋙ CommGrpCat.toAddCommGrp)

/-- The genuine finite-level tangent functor, before any representation. -/
def tangent (n : ℕ) : Test p R ⥤ AddCommGrpCat.{0} := kernel (evaluation p R G n)

/-- The original finite extension point inclusion into the formal point colimit. -/
def extensionInclusion (n : ℕ) : extensionPoints p R G n ⟶
    (PDivisibleLieModels.extensionPoints p R G ⋙ CommGrpCat.toAddCommGrp) :=
  Functor.whiskerLeft (extensionTests p R).rightOp
    (Functor.whiskerRight (levelInclusion (p := p) (S := Spec (.of R)) G n)
      CommGrpCat.toAddCommGrp)

/-- The same original inclusion on the underlying base tests. -/
def baseInclusion (n : ℕ) : basePoints p R G n ⟶
    (PDivisibleLieModels.basePoints p R G ⋙ CommGrpCat.toAddCommGrp) :=
  Functor.whiskerLeft (baseTests p R).rightOp
    (Functor.whiskerRight (levelInclusion (p := p) (S := Spec (.of R)) G n)
      CommGrpCat.toAddCommGrp)

/-- This square is the original point-inclusion naturality under augmentation. -/
theorem augmentation_square (n : ℕ) :
    extensionInclusion p R G n ≫
      Functor.whiskerRight (PDivisibleLieModels.evaluation p R G) CommGrpCat.toAddCommGrp =
    evaluation p R G n ≫ baseInclusion p R G n := by
  apply NatTrans.ext
  funext T
  exact ((Functor.whiskerRight
    (levelInclusion (p := p) (S := Spec (.of R)) G n) CommGrpCat.toAddCommGrp).naturality
      ((augmentations p R).app (op T)).op).symm

/-- The actual finite tangent maps to the actual formal tangent through native kernels. -/
def tangentInclusion (n : ℕ) : tangent p R G n ⟶ PDivisibleLieModels.tangentFunctor p R G :=
  kernel.map (evaluation p R G n)
    (Functor.whiskerRight (PDivisibleLieModels.evaluation p R G) CommGrpCat.toAddCommGrp)
    (extensionInclusion p R G n) (baseInclusion p R G n) (augmentation_square p R G n).symm

end MathlibExt.AlgebraicGeometry.PDivisibleFiniteTangentModels
