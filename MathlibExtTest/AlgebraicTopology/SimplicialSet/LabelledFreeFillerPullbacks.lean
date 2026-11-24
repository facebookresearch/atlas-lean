/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFillerPullbacks

/-!
# Public canonical pullback and native monicity clients
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SSet.LabelledFreeFillerPullbacksTest

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)
variable [∀ s, Mono (j s)] {X V Y Z : SSet.{u}}

/-- The native isomorphism uses the actual pullback comparison, for every span. -/
def canonicalIso (f : X ⟶ Y) (g : V ⟶ Y) :
    (labelledFreeFiller j).obj (pullback f g) ≅
      pullback ((labelledFreeFiller j).map f) ((labelledFreeFiller j).map g) :=
  PreservesPullback.iso (labelledFreeFiller j) f g

/-- The first comparison projection is the actual image of the original projection. -/
theorem canonicalIso_fst (f : X ⟶ Y) (g : V ⟶ Y) :
    (canonicalIso j f g).hom ≫ pullback.fst _ _ =
      (labelledFreeFiller j).map (pullback.fst f g) :=
  PreservesPullback.iso_hom_fst (labelledFreeFiller j) f g

/-- The second comparison projection is the actual image of the original projection. -/
theorem canonicalIso_snd (f : X ⟶ Y) (g : V ⟶ Y) :
    (canonicalIso j f g).hom ≫ pullback.snd _ _ =
      (labelledFreeFiller j).map (pullback.snd f g) :=
  PreservesPullback.iso_hom_snd (labelledFreeFiller j) f g

/-- Native monomorphism preservation cancels an equality of whole simplicial maps. -/
theorem wholeMapCancellation (m : X ⟶ Y) [Mono m]
    (a b : Z ⟶ (labelledFreeFiller j).obj X)
    (h : a ≫ (labelledFreeFiller j).map m = b ≫ (labelledFreeFiller j).map m) : a = b :=
  (cancel_mono ((labelledFreeFiller j).map m)).mp h

/-- Both maps may be the coproduct fold; no monicity premise on this span is needed. -/
theorem foldSpan (X : SSet.{u}) :
    let f : X ⨿ X ⟶ X := coprod.desc (𝟙 X) (𝟙 X)
    ∃ e : (labelledFreeFiller j).obj (pullback f f) ≅
      pullback ((labelledFreeFiller j).map f) ((labelledFreeFiller j).map f),
      e.hom ≫ pullback.fst _ _ = (labelledFreeFiller j).map (pullback.fst f f) ∧
      e.hom ≫ pullback.snd _ _ = (labelledFreeFiller j).map (pullback.snd f f) := by
  dsimp only
  exact ⟨canonicalIso j _ _, canonicalIso_fst j _ _, canonicalIso_snd j _ _⟩

end SSet.LabelledFreeFillerPullbacksTest
