/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado, Codex
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Initial maps in the Leibniz pushout

The chosen Leibniz pushout against an initial map is the unchanged first
functor map. The comparison identifies both pushout inclusions and keeps
the target literally fixed. Only the two actual empty-diagram preservation
assumptions are needed.
-/

@[expose] public section

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [HasPushouts C₃]

/-- Both chosen pushout cofans identify the original Leibniz map with the
first-variable functor map when the second source is initial. -/
def leibnizPushoutIsInitialRightIso (F : C₁ ⥤ C₂ ⥤ C₃)
    {X Y : C₁} (f : X ⟶ Y) {I : C₂} (hI : IsInitial I) (M : C₂)
    [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.obj X)]
    [PreservesColimitsOfShape (Discrete PEmpty.{1}) (F.obj Y)] :
    ((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk (hI.to M))) ≅
      Arrow.mk ((F.map f).app M) := by
  simp only [leibnizPushout_obj_obj, Arrow.mk_hom]
  let R := PushoutObjObj.ofHasPushout F f (hI.to M)
  let S := PushoutObjObj.ofIsInitialRight F f (hI.to M) hI
  let e : R.pt ≅ S.pt := R.isPushout.isoIsPushout _ _ S.isPushout
  have h₁ : R.inl ≫ e.hom = S.inl := R.isPushout.inl_isoIsPushout_hom _ _ S.isPushout
  have h₂ : R.inr ≫ e.hom = S.inr := R.isPushout.inr_isoIsPushout_hom _ _ S.isPushout
  have he : e.hom ≫ S.ι = R.ι := by
    apply R.isPushout.hom_ext
    · rw [← Category.assoc, h₁, S.inl_ι, R.inl_ι]
    · rw [← Category.assoc, h₂, S.inr_ι, R.inr_ι]
  exact Arrow.isoMk e (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id, Arrow.mk_hom]
    exact he)

end CategoryTheory.Functor
