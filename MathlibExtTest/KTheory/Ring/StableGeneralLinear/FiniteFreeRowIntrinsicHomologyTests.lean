/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowIntrinsicHomology

noncomputable section

open CategoryTheory Limits Algebra
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example :
    finiteFreeRowIntrinsicHomologyComparison R A q ≫
        (SInverseS.zeroLocalizedCoreHomologyIso
          (C := FGProjectiveCat.IdempotentModel R) A q).hom =
      finiteFreeRowHomologyColimitComparison R A q :=
  finiteFreeRowIntrinsicHomologyComparison_comp_homologyIso R A q

example (n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    ((finiteFreeRowIntrinsicHomologyComparison R A q
      (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q) n x)).val :
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
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q)
        ((finiteFreeRowRegularDenominator R) ^ n) :=
  finiteFreeRowIntrinsicHomologyComparison_ι_val R A q n x

example (n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q)
        ((finiteFreeRowRegularDenominator R) ^ n) ∈
      SInverseS.zeroLocalizedCoreSubgroup (C := FGProjectiveCat.IdempotentModel R) A q :=
  finiteFreeRowStageFraction_mem_zeroLocalizedCoreSubgroup R A q n x

end
