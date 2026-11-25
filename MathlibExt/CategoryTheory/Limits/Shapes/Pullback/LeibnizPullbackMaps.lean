/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-! # Characteristic maps of the original Leibniz construction -/

@[expose] public section

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.PullbackObjObj

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} [HasPullbacks C₂]

/-- Any given original pullback corner is compared with the actual canonical corner. -/
def canonicalArrowIso {A B : C₁} (j : A ⟶ B) {X Y : C₃} (p : X ⟶ Y)
    (sq : G.PullbackObjObj j p) :
    Arrow.mk sq.π ≅ (G.leibnizPullback.obj (op (Arrow.mk j))).obj (Arrow.mk p) :=
  π_iso_of_iso_right (G := G) (f₁ := Arrow.mk j)
    (f₃ := Arrow.mk p) (f₃' := Arrow.mk p) sq (ofHasPullback G j p) (Iso.refl _)

end CategoryTheory.Functor.PullbackObjObj
