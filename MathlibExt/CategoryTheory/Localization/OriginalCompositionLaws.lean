/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Localization.OriginalComparison

set_option autoImplicit false
universe u v u' v' uH vH
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {H : Type uH} [Category.{vH} H]

/-- Strict projection of two genuine Ho actions is the original full carrier composition. -/
theorem originalCompositionProjection (W : MorphismProperty C) (W' : MorphismProperty D)
    (F : C ⥤ D) (G : D ⥤ H)
    (FH : W.Localization ⥤ W'.Localization) (GH : W'.Localization ⥤ H)
    (hF : W.Q ⋙ FH = F ⋙ W'.Q) (hG : W'.Q ⋙ GH = G) :
    W.Q ⋙ (FH ⋙ GH) = F ⋙ G := by
  calc
    W.Q ⋙ (FH ⋙ GH) = (W.Q ⋙ FH) ⋙ GH := rfl
    _ = (F ⋙ W'.Q) ⋙ GH := by rw [hF]
    _ = F ⋙ (W'.Q ⋙ GH) := rfl
    _ = F ⋙ G := by rw [hG]

end CategoryTheory.Localization
