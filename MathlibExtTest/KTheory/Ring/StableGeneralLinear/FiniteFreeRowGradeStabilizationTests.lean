/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGradeStabilization

noncomputable section

open CategoryTheory Limits Algebra
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (n : ℕ)
    (c : CategoryTheory.ConnectedComponents
      (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))))
    (x : (nerve c.Component).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (k : ℕ)
      (y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ)).homology
        (C := AddCommGrpCat.{u}) A q),
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + k)) A q y =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (CategoryTheory.ConnectedComponents.ι c ⋙
            (SInverseS.coreGradeProperty (C := FGProjectiveCat.IdempotentModel R)
              (GrothendieckAddGroup.of
                (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι ⋙
            SInverseS.coreLeftTranslationFunctor
              ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k))) A q x :=
  finiteFreeRowGradeComponent_homology_exists_stage R A q n c x

end
