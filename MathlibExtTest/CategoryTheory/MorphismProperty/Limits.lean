/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.MorphismProperty.Limits

/-!
# Generic cobase-change API consumer tests

Focused consumer checks for `IsStableUnderCobaseChangeAgainst.of_isPushout`
and `IsStableUnderCobaseChangeAgainst.of_le`: method-syntax inference,
pushout-square orientation, and contravariant restriction in the right-hand
class.
-/

namespace CategoryTheory.MorphismProperty.LimitsTest

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {P Q R : MorphismProperty C}

-- Push a `P` leg through a pushout square along a `Q` leg via method syntax.
-- Catches binder/application regressions in `of_isPushout`.
example {X Y Z W : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (h : P.IsStableUnderCobaseChangeAgainst Q)
    (sq : IsPushout i f f' j) (hi : Q i) (hf : P f) : P f' :=
  h.of_isPushout sq hi hf

-- Contravariant restriction: stability against `Q` restricts to any `R ≤ Q`.
-- Catches variance-direction regressions in `of_le`.
example (h : P.IsStableUnderCobaseChangeAgainst Q) (hRQ : R ≤ Q) :
    P.IsStableUnderCobaseChangeAgainst R :=
  h.of_le hRQ

section SuppliedCofanAttachments

set_option autoImplicit false
noncomputable section

universe ν

-- A family of actual pushouts of given coproduct generator maps forms one
-- attachment of the primitive P family. The original outer endpoint is q;
-- no flattened cofan or aggregate pushout is rebuilt in this consumer.
example [HasCoproducts.{ν} C] {I : Type ν} (J : I → Type ν)
    {A B : ∀ i, J i → C} (p : ∀ i j, A i j ⟶ B i j)
    (hp : ∀ i j, P (p i j))
    (cA : ∀ i, Cofan (A i)) (cB : ∀ i, Cofan (B i))
    (hA : ∀ i, IsColimit (cA i)) (hB : ∀ i, IsColimit (cB i))
    (pCop : ∀ i, (cA i).pt ⟶ (cB i).pt)
    (hCop : ∀ i j, (cA i).inj j ≫ pCop i = p i j ≫ (cB i).inj j)
    {X Y : I → C} (a : ∀ i, (cA i).pt ⟶ X i)
    (b : ∀ i, (cB i).pt ⟶ Y i) (qCell : ∀ i, X i ⟶ Y i)
    (squares : ∀ i, IsPushout (a i) (pCop i) (qCell i) (b i))
    (cX : Cofan X) (cY : Cofan Y)
    (hX : IsColimit cX) (hY : IsColimit cY)
    (q : cX.pt ⟶ cY.pt)
    (hq : ∀ i, cX.inj i ≫ q = qCell i ≫ cY.inj i) :
    (coproducts.{ν} P).pushouts q := by
  have inner (i : I) : coproducts.{ν} P (pCop i) :=
    P.colimitsOfShape_le_coproducts (J i) _
      (colimitsOfShape.mk' (Discrete.functor (A i)) (Discrete.functor (B i))
        (cA i) (cB i) (hA i) (hB i)
        (Discrete.natTrans (fun j => p i j.as)) (fun j => hp i j.as)
        (pCop i) (fun j => hCop i j.as))
  have cells (i : I) : (coproducts.{ν} P).pushouts (qCell i) :=
    (coproducts.{ν} P).pushouts_mk (squares i) (inner i)
  have outer : coproducts.{ν} (coproducts.{ν} P).pushouts q :=
    (coproducts.{ν} P).pushouts.colimitsOfShape_le_coproducts I _
      (colimitsOfShape.mk' (Discrete.functor X) (Discrete.functor Y)
        cX cY hX hY (Discrete.natTrans (fun i => qCell i.as))
        (fun i => cells i.as) q (fun i => hq i.as))
  have twice : (coproducts.{ν} (coproducts.{ν} P)).pushouts q :=
    coproducts_pushouts_le (coproducts.{ν} P) q outer
  exact pushouts_monotone (coproducts_coproducts_le P) q twice

end

end SuppliedCofanAttachments

end CategoryTheory.MorphismProperty.LimitsTest
