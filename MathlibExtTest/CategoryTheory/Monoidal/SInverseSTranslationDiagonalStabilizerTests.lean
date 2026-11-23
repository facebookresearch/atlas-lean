/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalStabilizer

/-! # Tests for the canonical translation stabilizer class -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSTranslationDiagonalStabilizer

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translationStabilizerClass_diagonalAdd
#check coreTranslationCoefficientFunctor_map_diagonalAdd

example (A : C) (B : Translation C) :
    translationStabilizerClass C
        ((Translation.diagonalAddNatTrans A).app B) =
      toSkeleton A :=
  translationStabilizerClass_diagonalAdd C A B

#print axioms translationStabilizerClass_diagonalAdd
#print axioms coreTranslationCoefficientFunctor_map_diagonalAdd

end MathlibExtTest.SInverseSTranslationDiagonalStabilizer

end
