/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.SuccessorGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uJ vJ

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject CategoryTheory.SmallObject.CoherentRetracts

namespace CategoryTheory.SmallObject.CoherentRetractsPublicUse

/-- The caller's two chosen colimit points and all cocone legs are retained. -/
example {C : Type u} [Category.{v} C] {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SplitObject C)
    (cF : Cocone (D ⋙ SplitObject.sourceFunctor))
    (cG : Cocone (D ⋙ SplitObject.targetFunctor))
    (hF : IsColimit cF) (hG : IsColimit cG) :
    ∃ c : Cocone D, Nonempty (IsColimit c) ∧
      SplitObject.sourceFunctor.mapCocone c = cF ∧
      SplitObject.targetFunctor.mapCocone c = cG :=
  ⟨SplitObject.colimitCocone D cF cG hF hG,
    ⟨SplitObject.colimitIsColimit D cF cG hF hG⟩, rfl, rfl⟩

/-- Both source identities follow using only the particular normalization pushout. -/
example {C : Type u} [Category.{v} C] {X Y A B : C}
    (f : X ⟶ Y) (k : A ⟶ B) (R : RetractArrow f k) [HasPushout R.r.left k] :
    ∃ h : RetractArrow f (ArrowRetractRootNormalization.root R),
      h.i.left = 𝟙 X ∧ h.r.left = 𝟙 X ∧
      h.i.right = R.i.right ≫ pushout.inr R.r.left k ∧
      h.r.right = pushout.desc f R.r.right R.r_w :=
  ⟨ArrowRetractRootNormalization.arrowRetract R, rfl, rfl, rfl, rfl⟩

/-- The full successor map needs only the original source retraction identity. -/
example {C : Type u} [Category.{v} C] (X : SplitObject C) {Y Z : C}
    (f : X.source ⟶ Y) (g : X.source ⟶ Z) (R : RetractArrow f g)
    (hr : R.r.left = 𝟙 X.source) [HasPushout g X.inclusion] :
    ∃ h : X ⟶ SplitObject.successorObject X f g R hr,
      h.left = f ∧ h.right = pushout.inr g X.inclusion :=
  ⟨SplitObject.successorMap X f g R hr, rfl, rfl⟩

/-- Arbitrary class membership is transported through the two actual pushouts. -/
example {C : Type u} [Category.{v} C] (P : MorphismProperty C) (X : SplitObject C)
    {Y A B : C} (f : X.source ⟶ Y) (k : A ⟶ B) (R : RetractArrow f k)
    [HasPushout R.r.left k]
    [HasPushout (ArrowRetractRootNormalization.root R) X.inclusion] (hk : P k) :
    P.pushouts (SplitObject.successorMap X f (ArrowRetractRootNormalization.root R)
      (ArrowRetractRootNormalization.arrowRetract R) (by rfl)).right ∧
    IsPushout (R.r.left ≫ X.inclusion) k
      (SplitObject.successorMap X f (ArrowRetractRootNormalization.root R)
        (ArrowRetractRootNormalization.arrowRetract R) (by rfl)).right
      (ArrowRetractRootNormalization.oldTargetMap R ≫
        pushout.inl (ArrowRetractRootNormalization.root R) X.inclusion) :=
  ⟨SplitObject.originalSuccessor_mem P X f k R hk,
    SplitObject.originalSuccessorPushout X f k R⟩

end CategoryTheory.SmallObject.CoherentRetractsPublicUse
