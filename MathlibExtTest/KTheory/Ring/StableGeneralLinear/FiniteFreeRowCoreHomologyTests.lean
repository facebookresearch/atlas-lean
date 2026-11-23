/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreHomology

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R] (A : AddCommGrpCat.{u}) (q : ℕ)

example (n : ℕ) :
    finiteFreeRowCoreComponentNerveMap R n ≫
        nerveMap (CategoryTheory.ConnectedComponents.ι
          (CategoryTheory.ConnectedComponents.mk
            (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))) =
      finiteFreeRowStageCoreNerveMap R n :=
  finiteFreeRowCoreComponentNerveMap_comp_inclusion R n

example (n : ℕ) :
    Mono (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q) :=
  finiteFreeRowStageCoreHomology_mono R A q n

example (n : ℕ)
    (x y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q)
    (h : SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (finiteFreeRowStageCoreNerveMap R n) A q y) : x = y := by
  letI : Mono (SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R n) A q) :=
    finiteFreeRowStageCoreHomology_mono R A q n
  exact ((AddCommGrpCat.mono_iff_injective _).mp inferInstance) h

end
