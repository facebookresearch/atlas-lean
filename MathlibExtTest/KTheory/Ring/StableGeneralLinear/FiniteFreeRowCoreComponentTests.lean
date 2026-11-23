/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreComponent

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL

universe u

variable (R : Type u) [Ring R]

example (n : ℕ) (Z : Core (FGProjectiveCat.IdempotentModel R)) :
    Nonempty (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅ Z.of) ↔
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).objectProperty Z :=
  finiteFreeRowCore_isoclass_iff_component R n Z

example (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≌
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))).Component :=
  finiteFreeRowCoreComponentEquivalence R n

example (n : ℕ) :
    (finiteFreeRowCoreComponentEquivalence R n).functor ⋙
        CategoryTheory.ConnectedComponents.ι
          (CategoryTheory.ConnectedComponents.mk
            (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))) =
      finiteFreeRowCoreModelFunctor R n := by
  rw [finiteFreeRowCoreComponentEquivalence_functor]
  exact finiteFreeRowCoreComponentFunctor_comp_inclusion R n

end
