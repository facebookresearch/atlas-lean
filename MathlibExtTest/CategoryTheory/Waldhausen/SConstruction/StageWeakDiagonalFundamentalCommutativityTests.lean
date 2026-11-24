/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalFundamentalCommutativity

/-!
# Weak-diagonal fundamental-group commutativity tests

These tests pin the reversed `End` multiplication in the cofiber relation,
pairwise object-generator commutativity, and arbitrary multiplication
commutativity under only the Waldhausen hypotheses.  They install no
commutative-group instance and make no K-zero, encode/decode, realization,
loop-space, additivity-equivalence, spectrum, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalFundamentalCommutativityTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example : Type (max u v) := stageWeakDiagonalFundamentalGroup C

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    stageWeakDiagonalObjectGenerator C Z *
        stageWeakDiagonalObjectGenerator C X =
      stageWeakDiagonalObjectGenerator C Y :=
  stageWeakDiagonalObjectGenerator_quotient_mul_source C f g hSeq

example (A B : C) :
    stageWeakDiagonalObjectGenerator C A *
        stageWeakDiagonalObjectGenerator C B =
      stageWeakDiagonalObjectGenerator C B *
        stageWeakDiagonalObjectGenerator C A :=
  stageWeakDiagonalObjectGenerator_comm C A B

example (f g : stageWeakDiagonalFundamentalGroup C) :
    f * g = g * f :=
  stageWeakDiagonalFundamentalGroup_mul_comm C f g

end StageWeakDiagonalFundamentalCommutativityTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
