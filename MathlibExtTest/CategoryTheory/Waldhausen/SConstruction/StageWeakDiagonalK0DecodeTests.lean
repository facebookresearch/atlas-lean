/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Decode

/-!
# Combinatorial weak-diagonal K-zero decode tests

These tests pin the left-stage edge valuation, the generic every-`CompStruct`
relation and its source-then-quotient orientation, the fundamental-groupoid
functor computations, and the based decode homomorphism.  They make no
commutativity, encode, inverse, realization, additivity, spectrum, or Q/S
claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0DecodeTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

variable {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
  (e : (stageWeakDiagonal C).Edge x y)

example : CategoryTheory.End
    (SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C))) :=
  stageWeakDiagonalK0EdgeValue C e

example : stageWeakDiagonalK0EdgeValue C e =
    SingleObj.toEnd _
      (Multiplicative.ofAdd
        (WaldhausenKTheory.K0.mk
          ((stageOneEval C).obj (ComposableArrows.left e.edge).obj))) :=
  rfl

example {x₀ x₁ x₂ : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    {e₀₁ : (stageWeakDiagonal C).Edge x₀ x₁}
    {e₁₂ : (stageWeakDiagonal C).Edge x₁ x₂}
    {e₀₂ : (stageWeakDiagonal C).Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (stageWeakDiagonalK0EdgeValue C e₀₁).asHom ≫
      (stageWeakDiagonalK0EdgeValue C e₁₂).asHom =
        (stageWeakDiagonalK0EdgeValue C e₀₂).asHom :=
  stageWeakDiagonalK0EdgeValue_comp C h

example : SSet.FundamentalGroupoid (stageWeakDiagonal C) ⥤
    SingleObj (Multiplicative (WaldhausenKTheory.K0 C)) :=
  stageWeakDiagonalK0Functor C

example (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonalK0Functor C).obj
        (SSet.FundamentalGroupoid.mk x) =
      SingleObj.star (Multiplicative (WaldhausenKTheory.K0 C)) :=
  stageWeakDiagonalK0Functor_obj_mk C x

example :
    (stageWeakDiagonalK0Functor C).map
        (SSet.FundamentalGroupoid.homMk e) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.mk
          ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)) :=
  stageWeakDiagonalK0Functor_map_homMk C e

example (A : C) :
    (stageWeakDiagonalK0Functor C).map
        (stageWeakDiagonalObjectGenerator C A).asHom =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A) :=
  stageWeakDiagonalK0Functor_map_objectGenerator C A

example : stageWeakDiagonalFundamentalGroup C →*
    Multiplicative (WaldhausenKTheory.K0 C) :=
  stageWeakDiagonalFundamentalToK0 C

example (A : C) :
    stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalObjectGenerator C A) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk A) :=
  stageWeakDiagonalFundamentalToK0_objectGenerator C A

section CofiberOrientation

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hSeq : IsCofibrationSequence (C := C) f g)

example :
    (stageWeakDiagonalK0EdgeValue C
          (stageWeakDiagonalObjectEdge C X)).asHom ≫
        (stageWeakDiagonalK0EdgeValue C
          (stageWeakDiagonalObjectEdge C Z)).asHom =
      (stageWeakDiagonalK0EdgeValue C
        (stageWeakDiagonalObjectEdge C Y)).asHom :=
  stageWeakDiagonalK0EdgeValue_comp C
    (stageWeakDiagonalCofiberCompStruct C f g hSeq)

end CofiberOrientation

end StageWeakDiagonalK0DecodeTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
