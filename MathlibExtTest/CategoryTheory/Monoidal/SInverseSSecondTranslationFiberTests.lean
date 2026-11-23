/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFiber

/-! # Tests for second translation on strict additive S⁻¹S fibers -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationFiber

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check secondTranslationFiberFunctor
#check secondTranslationFiberFunctor_obj_val
#check secondTranslationFiberFunctor_map_val

example (A : C) (B : Translation C) :
    (translationProjection (C := C)).Fiber B ⥤
      (translationProjection (C := C)).Fiber B :=
  secondTranslationFiberFunctor A B

#print axioms secondTranslationFiberFunctor

end MathlibExtTest.SInverseSSecondTranslationFiber

end
