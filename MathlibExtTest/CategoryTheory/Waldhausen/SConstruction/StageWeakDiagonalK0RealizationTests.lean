/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Realization

/-! Public consumers for the realized weak-diagonal K-zero comparison. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0RealizationTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategory C]

example :
    _root_.FundamentalGroupoid.mk
        (SSet.realizedVertex (stageWeakDiagonalZeroVertex C)) ≅
      _root_.FundamentalGroupoid.mk
        (stageWeakDiagonalReal.basepoint C) :=
  stageWeakDiagonalRealizedVertexBasepointIso C

example : stageWeakDiagonalFundamentalGroup C ≃*
    FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C) :=
  stageWeakDiagonalRealizationFundamentalMulEquiv C

example : FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C) ≃*
    Multiplicative (WaldhausenKTheory.K0 C) :=
  stageWeakDiagonalRealizedFundamentalK0MulEquiv C

example : Additive (FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C)) ≃+
    WaldhausenKTheory.K0 C :=
  stageWeakDiagonalRealizedFundamentalK0AddEquiv C

example : ZerothHomotopy (stageWeakDiagonalKSpace C) ≃
    WaldhausenKTheory.K0 C :=
  stageWeakDiagonalKSpacePiZeroEquivK0 C

example (X : C) : stageWeakDiagonalKSpace C :=
  stageWeakDiagonalObjectLoop C X

example (X : C) :
    stageWeakDiagonalRealizationFundamentalMulEquiv C
        (stageWeakDiagonalObjectGenerator C X) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (stageWeakDiagonalObjectLoop C X)) :=
  stageWeakDiagonalRealizationFundamentalMulEquiv_objectGenerator C X

example (X : C) :
    stageWeakDiagonalKSpacePiZeroEquivK0 C
        (ZerothHomotopy.mk (stageWeakDiagonalObjectLoop C X)) =
      WaldhausenKTheory.K0.mk X :=
  stageWeakDiagonalKSpacePiZeroEquivK0_objectLoop C X

example (X : C) :
    stageWeakDiagonalObjectLoop C X 0 =
      stageWeakDiagonalReal.basepoint C :=
  (stageWeakDiagonalObjectLoop C X).source

example (X : C) :
    stageWeakDiagonalObjectLoop C X 1 =
      stageWeakDiagonalReal.basepoint C :=
  (stageWeakDiagonalObjectLoop C X).target

section UniverseZero

variable (C₀ : Type) [Category C₀] [HasZeroObject C₀]
  [WaldhausenCategory C₀]

example : ZerothHomotopy (stageWeakDiagonalKSpace C₀) ≃
    WaldhausenKTheory.K0 C₀ :=
  stageWeakDiagonalKSpacePiZeroEquivK0 C₀

end UniverseZero

section UniverseOne

variable (C₁ : Type 1) [Category.{1} C₁] [HasZeroObject C₁]
  [WaldhausenCategory C₁]

example : ZerothHomotopy (stageWeakDiagonalKSpace C₁) ≃
    WaldhausenKTheory.K0 C₁ :=
  stageWeakDiagonalKSpacePiZeroEquivK0 C₁

end UniverseOne

#print axioms stageWeakDiagonalRealizedVertexBasepointIso
#print axioms stageWeakDiagonalRealizationFundamentalMulEquiv
#print axioms stageWeakDiagonalRealizedFundamentalK0MulEquiv
#print axioms stageWeakDiagonalRealizedFundamentalK0AddEquiv
#print axioms stageWeakDiagonalKSpacePiZeroEquivK0
#print axioms stageWeakDiagonalObjectLoop
#print axioms
  stageWeakDiagonalRealizationFundamentalMulEquiv_objectGenerator
#print axioms stageWeakDiagonalKSpacePiZeroEquivK0_objectLoop

end StageWeakDiagonalK0RealizationTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
