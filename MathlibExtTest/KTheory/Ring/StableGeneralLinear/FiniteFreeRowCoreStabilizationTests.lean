/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreStabilization

noncomputable section

open CategoryTheory Limits Algebra
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (n : ℕ) :
    SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.coreLeftTranslationFunctor
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) A q =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + 1)) A q :=
  finiteFreeRowStageCoreHomology_stabilization_square R A q n

example (n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).inv
      (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + 1)) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) A q x)) =
      @SMul.smul
        ↥(SInverseS.coreTranslationDenominators (FGProjectiveCat.IdempotentModel R))
        (SInverseS.coreTranslationHomologyModuleCat
          (FGProjectiveCat.IdempotentModel R) A q)
        inferInstance (finiteFreeRowRegularDenominator R)
        (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u})
              (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q) :=
  finiteFreeRowStageCoreNumerator_succ R A q n x

end
