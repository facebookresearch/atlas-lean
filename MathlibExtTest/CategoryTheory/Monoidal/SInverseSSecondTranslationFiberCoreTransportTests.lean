/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiberCoreTransport

/-! # Tests for transported fiberwise second/core translation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationFiberCoreTransport

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check coreSecondTranslationFiber_obj_eq
#check coreSecondTranslationFiber_map_heq
#check coreSecondTranslationFiberFunctor_eq
#check coreSecondTranslationFiberIso

example (A B : Core C) :
    coreToTranslationFiber B ⋙
        secondTranslationFiberFunctor A.of
          (⟨B.of⟩ : Translation C) ≅
      coreLeftTranslationFunctor A.of ⋙ coreToTranslationFiber B :=
  coreSecondTranslationFiberIso A B

#print axioms coreSecondTranslationFiberFunctor_eq
#print axioms coreSecondTranslationFiberIso

end MathlibExtTest.SInverseSSecondTranslationFiberCoreTransport

end
