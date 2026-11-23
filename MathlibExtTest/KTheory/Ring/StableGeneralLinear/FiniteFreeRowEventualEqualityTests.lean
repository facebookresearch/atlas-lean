/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowEventualEquality

noncomputable section

open CategoryTheory Limits Algebra
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (n m : ℕ) (h : n ≤ m)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).inv
      (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R m) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE h)) A q x)) =
      @SMul.smul
        ↥(SInverseS.coreTranslationDenominators (FGProjectiveCat.IdempotentModel R))
        (SInverseS.coreTranslationHomologyModuleCat
          (FGProjectiveCat.IdempotentModel R) A q)
        inferInstance ((finiteFreeRowRegularDenominator R) ^ (m - n))
        ((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u})
              (finiteFreeRowStageCoreNerveMap R n) A q x)) :=
  finiteFreeRowStageCoreNumerator_stabilization R A q n m h x

example (n m : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q)
    (y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    finiteFreeRowIntrinsicHomologyComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) n x) =
      finiteFreeRowIntrinsicHomologyComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) m y) ↔
      ∃ (t : ℕ) (hn : n ≤ t) (hm : m ≤ t),
        SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE hn)) A q x =
          SSet.homologyMap (C := AddCommGrpCat.{u})
            ((finiteBGLNerveDiagram R).map (homOfLE hm)) A q y :=
  finiteFreeRowIntrinsic_stage_eq_iff_common_stage R A q n m x y

example : Mono (finiteFreeRowIntrinsicHomologyComparison R A q) :=
  finiteFreeRowIntrinsicHomologyComparison_mono R A q

end
