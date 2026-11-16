/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

/-!
The structural coefficients are literal thickening rings, rather than
functions on reduced points. The Ext object and its cochains are checked
against the actual group and structure sheaves in their full native site.
-/

open CategoryTheory Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests
open MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.CategoryTheory.SheafInternalExtModels

noncomputable section

variable (p : ℕ) [Fact p.Prime] (A : PDBase) (S : Over A.reduction)

example (P : Obj p A S) :
    (structureRingPresheaf p A S).obj (op P) = CommRingCat.of (ULift.{1} P.ring) := rfl

example {P Q : Obj p A S} (f : P ⟶ Q) (a : Q.ring) :
    ((structureRingPresheaf p A S).map f.op).hom (ULift.up a) =
      ULift.up (f.algebra a) := rfl

example (G : PDivisibleGroup S.left p) :
    crystallineExt p A S G = internalExt (topology p A S)
      (groupSheaf p A S G) (structureSheaf p A S) 1 := rfl

example (G : PDivisibleGroup S.left p) :
    crystallineExt p A S G ≅ (crystallineExtCochains p A S G).homology 1 :=
  crystallineExtResolutionIso p A S G

#print axioms MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests.reductions
#print axioms MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests.cover_mem
#print axioms MathlibExt.CategoryTheory.SheafInternalExtModels.homSheaf
#print axioms MathlibExt.CategoryTheory.SheafInternalExtModels.homFunctor
#print axioms MathlibExt.CategoryTheory.SheafInternalExtModels.internalExtResolutionIso
#print axioms MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves.crystallineExt
#print axioms
  MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves.crystallineExtResolutionIso
