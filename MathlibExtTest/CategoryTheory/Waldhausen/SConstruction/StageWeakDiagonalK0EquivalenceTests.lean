/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Equivalence

/-!
# Combinatorial weak-diagonal K-zero equivalence tests

These tests pin the multiplicative encode formulas, both inverse laws, and
the decode-forward multiplicative and additive equivalence computations.
They make no realization, topological `pi_0`, additivity-map, spectrum, or
Q/S claim and install no algebraic instance.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0EquivalenceTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example : Multiplicative (WaldhausenKTheory.K0 C) →*
    stageWeakDiagonalFundamentalGroup C :=
  stageWeakDiagonalK0EncodeMul C

example (x : WaldhausenKTheory.K0 C) :
    stageWeakDiagonalK0EncodeMul C (Multiplicative.ofAdd x) =
      Additive.toMul (stageWeakDiagonalK0Encode C x) :=
  stageWeakDiagonalK0EncodeMul_ofAdd C x

example (X : C) :
    stageWeakDiagonalK0EncodeMul C
        (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X)) =
      stageWeakDiagonalObjectGenerator C X :=
  stageWeakDiagonalK0EncodeMul_mk C X

example :
    (MonoidHom.toAdditiveLeft
        (stageWeakDiagonalFundamentalToK0 C)).comp
      (stageWeakDiagonalK0Encode C) =
    AddMonoidHom.id (WaldhausenKTheory.K0 C) :=
  stageWeakDiagonalK0DecodeAdd_comp_encode C

example (x : Multiplicative (WaldhausenKTheory.K0 C)) :
    stageWeakDiagonalFundamentalToK0 C
        (stageWeakDiagonalK0EncodeMul C x) = x :=
  stageWeakDiagonalK0Decode_encodeMul C x

example (f : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalK0EncodeMul C
        (stageWeakDiagonalFundamentalToK0 C f) = f :=
  stageWeakDiagonalK0EncodeMul_decode C f

example : stageWeakDiagonalFundamentalGroup C ≃*
    Multiplicative (WaldhausenKTheory.K0 C) :=
  stageWeakDiagonalFundamentalK0MulEquiv C

example (f : stageWeakDiagonalFundamentalGroup C) :
    stageWeakDiagonalFundamentalK0MulEquiv C f =
      stageWeakDiagonalFundamentalToK0 C f :=
  stageWeakDiagonalFundamentalK0MulEquiv_apply C f

example (x : Multiplicative (WaldhausenKTheory.K0 C)) :
    (stageWeakDiagonalFundamentalK0MulEquiv C).symm x =
      stageWeakDiagonalK0EncodeMul C x :=
  stageWeakDiagonalFundamentalK0MulEquiv_symm_apply C x

example (X : C) :
    stageWeakDiagonalFundamentalK0MulEquiv C
        (stageWeakDiagonalObjectGenerator C X) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X) :=
  stageWeakDiagonalFundamentalK0MulEquiv_objectGenerator C X

example (X : C) :
    (stageWeakDiagonalFundamentalK0MulEquiv C).symm
        (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X)) =
      stageWeakDiagonalObjectGenerator C X :=
  stageWeakDiagonalFundamentalK0MulEquiv_symm_mk C X

example : Additive (stageWeakDiagonalFundamentalGroup C) ≃+
    WaldhausenKTheory.K0 C :=
  stageWeakDiagonalFundamentalK0AddEquiv C

example (f : Additive (stageWeakDiagonalFundamentalGroup C)) :
    stageWeakDiagonalFundamentalK0AddEquiv C f =
      Multiplicative.toAdd
        (stageWeakDiagonalFundamentalToK0 C (Additive.toMul f)) :=
  stageWeakDiagonalFundamentalK0AddEquiv_apply C f

example (x : WaldhausenKTheory.K0 C) :
    (stageWeakDiagonalFundamentalK0AddEquiv C).symm x =
      stageWeakDiagonalK0Encode C x :=
  stageWeakDiagonalFundamentalK0AddEquiv_symm_apply C x

example (X : C) :
    stageWeakDiagonalFundamentalK0AddEquiv C
        (Additive.ofMul (stageWeakDiagonalObjectGenerator C X)) =
      WaldhausenKTheory.K0.mk X :=
  stageWeakDiagonalFundamentalK0AddEquiv_objectGenerator C X

example (X : C) :
    (stageWeakDiagonalFundamentalK0AddEquiv C).symm
        (WaldhausenKTheory.K0.mk X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) :=
  stageWeakDiagonalFundamentalK0AddEquiv_symm_mk C X

end StageWeakDiagonalK0EquivalenceTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
