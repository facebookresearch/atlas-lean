/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowFractionRegularization

noncomputable section

open CategoryTheory Limits Algebra
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (t : Skeleton (FGProjectiveCat.IdempotentModel R))
    (y : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
      (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (n : ℕ)
      (z : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))))).homology
            (C := AddCommGrpCat.{u}) A q),
      (SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q t y :
        CategoryTheory.SInverseS.localizedCoreTranslationHomology
          (FGProjectiveCat.IdempotentModel R) A q) =
        LocalizedModule.mk
          (R := CategoryTheory.SInverseS.coreTranslationRing
            (FGProjectiveCat.IdempotentModel R))
          (S := CategoryTheory.SInverseS.coreTranslationDenominators
            (FGProjectiveCat.IdempotentModel R))
          (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
            (FGProjectiveCat.IdempotentModel R) A q)
          (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
            (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (SInverseS.coreGradeProperty
              (C := FGProjectiveCat.IdempotentModel R)
              (GrothendieckAddGroup.of
                (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι) A q z)) :
            CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
              (FGProjectiveCat.IdempotentModel R) A q)
          ((finiteFreeRowRegularDenominator R) ^ n) :=
  finiteFreeRowZeroFraction_exists_regular_grade R A q t y

end
