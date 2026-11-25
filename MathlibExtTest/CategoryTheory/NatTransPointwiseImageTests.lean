/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.CategoryTheory.NatTrans.PointwiseImage
import Mathlib.CategoryTheory.Discrete.Basic

/-! # Tests for pointwise image functors -/

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace MathlibExtTest.CategoryTheory.NatTransPointwiseImageTests

variable {B : Type u₁} [Category.{v₁} B]
variable {I : Type u₂} [Category.{v₂} I]
variable {C : Type u₃} [Category.{v₃} C]
variable [HasImages C] [HasImageMaps C]

variable {F G : B ⥤ I ⥤ C} (α : F ⟶ G)

noncomputable example : B ⥤ I ⥤ C :=
  α.pointwiseImage

example (b : B) (i : I) :
    (α.pointwiseImage.obj b).obj i = image ((α.app b).app i) := by
  simp

example (b : B) {i i' : I} (f : i ⟶ i') :
    (α.pointwiseImage.obj b).map f =
      image.map
        (Arrow.homMk ((F.obj b).map f) ((G.obj b).map f)
          ((α.app b).naturality f)) := by
  simp

example {b b' : B} (f : b ⟶ b') (i : I) :
    (α.pointwiseImage.map f).app i =
      image.map
        (Arrow.homMk ((F.map f).app i) ((G.map f).app i)
          (congr_app (α.naturality f) i)) := by
  simp

example (b : B) :
    α.pointwiseImage.map (𝟙 b) = 𝟙 (α.pointwiseImage.obj b) :=
  α.pointwiseImage.map_id b

example {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    α.pointwiseImage.map (f ≫ g) =
      α.pointwiseImage.map f ≫ α.pointwiseImage.map g :=
  α.pointwiseImage.map_comp f g

example (H : B ⥤ I ⥤ C) (b : B) (i : I) :
    (((𝟙 H : H ⟶ H).pointwiseImage.obj b).obj i) =
      image (𝟙 ((H.obj b).obj i)) := by
  simp

section TerminalIndex

variable {F' G' : B ⥤ Discrete PUnit ⥤ C} (β : F' ⟶ G')

example (b : B) :
    (β.pointwiseImage.obj b).obj (Discrete.mk PUnit.unit) =
      image ((β.app b).app (Discrete.mk PUnit.unit)) := by
  simp

end TerminalIndex

#print axioms CategoryTheory.NatTrans.pointwiseImage

end MathlibExtTest.CategoryTheory.NatTransPointwiseImageTests
