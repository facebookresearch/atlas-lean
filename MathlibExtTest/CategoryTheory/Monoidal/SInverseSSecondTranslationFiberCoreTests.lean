/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiberCore

/-! # Tests for the fiberwise second/core translation comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationFiberCore

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translateSecond_coreTranslationFiberRawMap_rel
#check explicitCoreFiberRawMap
#check explicitCoreSecondTranslationRawMap

#print axioms translateSecond_coreTranslationFiberRawMap_rel
#print axioms explicitCoreFiberRawMap
#print axioms explicitCoreSecondTranslationRawMap

end MathlibExtTest.SInverseSSecondTranslationFiberCore

end
