/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Encode

/-!
# Combinatorial weak-diagonal K-zero encode tests

These tests pin the named non-instance additive-commutative witness,
skeleton-representative transport, weak and cofiber relations, the additive
encode, and its object-generator law.  They make no inverse, equivalence,
realization, topology, additivity, spectrum, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalK0EncodeTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example : AddCommGroup
    (Additive (stageWeakDiagonalFundamentalGroup C)) :=
  stageWeakDiagonalFundamentalAddCommGroup C

example (f g : Additive (stageWeakDiagonalFundamentalGroup C)) :
    f + g = g + f := by
  let _ : AddCommGroup
      (Additive (stageWeakDiagonalFundamentalGroup C)) :=
    stageWeakDiagonalFundamentalAddCommGroup C
  exact add_comm f g

example (s : Skeleton C) :
    Additive (stageWeakDiagonalFundamentalGroup C) :=
  stageWeakDiagonalK0EncodeGenerator C s

example (X : C) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) :=
  stageWeakDiagonalK0EncodeGenerator_toSkeleton C X

example {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) =
      stageWeakDiagonalK0EncodeGenerator C (toSkeleton Y) :=
  stageWeakDiagonalK0Encode_weak C f hf

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    stageWeakDiagonalK0EncodeGenerator C (toSkeleton Y) =
      stageWeakDiagonalK0EncodeGenerator C (toSkeleton X) +
        stageWeakDiagonalK0EncodeGenerator C (toSkeleton Z) :=
  stageWeakDiagonalK0Encode_cofiber C f g hSeq

example : WaldhausenKTheory.K0 C →+
    Additive (stageWeakDiagonalFundamentalGroup C) :=
  stageWeakDiagonalK0Encode C

example (X : C) :
    stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X) =
      Additive.ofMul (stageWeakDiagonalObjectGenerator C X) :=
  stageWeakDiagonalK0Encode_mk C X

example {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X) =
      stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk Y) := by
  rw [WaldhausenKTheory.K0.mk_eq_of_weakEquivalence f hf]

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk Y) =
      stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk X) +
        stageWeakDiagonalK0Encode C (WaldhausenKTheory.K0.mk Z) := by
  rw [WaldhausenKTheory.K0.mk_eq_of_cofibrationSequence hSeq, map_add]

end StageWeakDiagonalK0EncodeTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
