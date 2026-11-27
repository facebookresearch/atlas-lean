/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.MorphismProperty.Limits
import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Supplied coproduct and pushout composition consumer

Use actual component composition witnesses, original colimiting cofans and the
actual endpoint pushout to retain the final arrow and the same ordered shape.
The attaching class is derived from the primitive generator family.
-/

namespace CategoryTheory.MorphismProperty.TransfiniteCompositionTest

open CategoryTheory Limits

set_option autoImplicit false
noncomputable section

universe ν κ vC uC

variable {C : Type uC} [Category.{vC} C]
variable {K : Type κ} [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]

-- Classify the original final q using supplied cofans and its actual pushout.
-- The coproduct closure of the attachment family follows from the earlier
-- coproduct helpers; the consumer does not assume that desired closure.
example [HasCoproducts.{ν} C] {I : Type ν} (T : MorphismProperty C)
    {S Y : I → C} (p : ∀ i, S i ⟶ Y i)
    (cp : ∀ i, (coproducts.{ν} T).pushouts.TransfiniteCompositionOfShape K (p i))
    (cS : Cofan S) (cY : Cofan Y) (hS : IsColimit cS) (hY : IsColimit cY)
    (pCop : cS.pt ⟶ cY.pt)
    (hCop : ∀ i, cS.inj i ≫ pCop = p i ≫ cY.inj i)
    {X Z : C} (a : cS.pt ⟶ X) [HasPushoutsAlong a]
    {q : X ⟶ Z} {b : cY.pt ⟶ Z} (sq : IsPushout a pCop q b) :
    (coproducts.{ν} T).pushouts.TransfiniteCompositionOfShape K q := by
  classical
  let A : MorphismProperty C := (coproducts.{ν} T).pushouts
  have hA : coproducts.{ν} A ≤ A :=
    le_trans (coproducts_pushouts_le (coproducts.{ν} T))
      (pushouts_monotone (coproducts_coproducts_le T))
  have outer : coproducts.{ν} (A.transfiniteCompositionsOfShape K) pCop :=
    (A.transfiniteCompositionsOfShape K).colimitsOfShape_le_coproducts I _
      (colimitsOfShape.mk' (Discrete.functor S) (Discrete.functor Y)
        cS cY hS hY (Discrete.natTrans (fun i => p i.as))
        (fun i => ⟨cp i.as⟩) pCop (fun i => hCop i.as))
  have distributed : (coproducts.{ν} A).transfiniteCompositionsOfShape K pCop :=
    coproducts_transfiniteCompositionsOfShape_le A K pCop outer
  let composition : A.TransfiniteCompositionOfShape K pCop :=
    distributed.some.ofLE hA
  let pushed : A.pushouts.TransfiniteCompositionOfShape K q :=
    composition.cobaseChange a sq
  exact pushed.ofLE (pushouts_le (P := A))

end

end CategoryTheory.MorphismProperty.TransfiniteCompositionTest
