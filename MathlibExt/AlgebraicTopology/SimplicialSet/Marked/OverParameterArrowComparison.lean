/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterLeibniz
import MathlibExt.CategoryTheory.Comma.Over.ArrowIso

/-!
# The same original marked parameter corner in its fixed-base slice

Forgetting only the slice records keeps the actual marked pushout point.
The two native pushout squares compare their whole corner maps by an
isomorphism whose target map is exactly the identity. Thus the original
base projection is preserved, rather than replaced by an arbitrary
base operator.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked

/-- Forgetting the original slice gives the same full marked corner through its native pushout-point isomorphism. -/
def overParameterMarkedArrowIso {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) :
    Arrow.mk (overParameterPushoutProduct a f).left ≅ Arrow.mk (parameterPushoutProduct a f.left) := by
  let s := overParameterUnderlyingPushout a f
  let t := parameterPushout a f.left
  exact Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk f.left) (f₂ := Arrow.mk a) (f₂' := Arrow.mk a)
    s t (Iso.refl (Arrow.mk a))

/-- The complete target component retains the original marked target by the identity map. -/
@[simp]
theorem overParameterMarkedArrowIso_hom_right {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) :
    (overParameterMarkedArrowIso a f).hom.right = 𝟙 (prod (max D) Y.left) := by
  change (maxTensorBifunctor.obj Y.left).map (𝟙 D) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- Every original slice arrow is the same arrow with its source base map written as the full supplied triangle. -/
def overArrowNormalizationIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (Over.homMk f.left rfl : Over.mk (f.left ≫ Y.hom) ⟶ Y) :=
  Arrow.isoMk (Over.isoMk (Iso.refl X.left) (by
      change 𝟙 X.left ≫ (f.left ≫ Y.hom) = X.hom
      exact (Category.id_comp _).trans (Over.w f)))
    (Iso.refl Y) (by
      apply Over.OverMorphism.ext
      change 𝟙 X.left ≫ f.left = f.left ≫ 𝟙 Y.left
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The original marked parameter corner lifts to exactly the same whole fixed-base corner, with no change
  of its base map. -/
def overParameterOriginalCornerIso {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) :
    Arrow.mk (overParameterPushoutProduct a f) ≅
      Arrow.mk (Over.homMk (parameterPushoutProduct a f.left) rfl :
        Over.mk (parameterPushoutProduct a f.left ≫ prodSnd (max D) Y.left ≫ Y.hom) ⟶
          overParameter Z Y D) := by
  let e := overParameterMarkedArrowIso a f
  exact overArrowNormalizationIso (overParameterPushoutProduct a f) ≪≫
    Arrow.isoOver e _ _ (by rw [overParameterMarkedArrowIso_hom_right]; exact Category.id_comp _)

end SSet.Marked
