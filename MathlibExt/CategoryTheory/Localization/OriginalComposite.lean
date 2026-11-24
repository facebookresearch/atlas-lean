/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Localization.Predicate

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C]

/-- The complete original composite lift equals the composite action through its true projection. -/
def originalCompositeIso (W : MorphismProperty C) (F G : C ⥤ C)
    (hF : W.IsInvertedBy (F ⋙ W.Q)) (hG : W.IsInvertedBy (G ⋙ W.Q))
    (hFG : W.IsInvertedBy ((F ⋙ G) ⋙ W.Q)) :
    Construction.lift ((F ⋙ G) ⋙ W.Q) hFG ≅
      Construction.lift (F ⋙ W.Q) hF ⋙ Construction.lift (G ⋙ W.Q) hG := by
  let _ : Lifting W.Q W ((F ⋙ G) ⋙ W.Q)
      (Construction.lift ((F ⋙ G) ⋙ W.Q) hFG) := ⟨eqToIso (Construction.fac _ _)⟩
  let _ : Lifting W.Q W ((F ⋙ G) ⋙ W.Q)
      (Construction.lift (F ⋙ W.Q) hF ⋙ Construction.lift (G ⋙ W.Q) hG) :=
    ⟨eqToIso (by
      calc
        W.Q ⋙ (Construction.lift (F ⋙ W.Q) hF ⋙ Construction.lift (G ⋙ W.Q) hG) =
            (W.Q ⋙ Construction.lift (F ⋙ W.Q) hF) ⋙ Construction.lift (G ⋙ W.Q) hG := rfl
        _ = (F ⋙ W.Q) ⋙ Construction.lift (G ⋙ W.Q) hG := by rw [Construction.fac]
        _ = F ⋙ (W.Q ⋙ Construction.lift (G ⋙ W.Q) hG) := rfl
        _ = F ⋙ (G ⋙ W.Q) := by rw [Construction.fac]
        _ = _ := rfl)⟩
  exact liftNatIso W.Q W ((F ⋙ G) ⋙ W.Q) ((F ⋙ G) ⋙ W.Q)
    (Construction.lift ((F ⋙ G) ⋙ W.Q) hFG)
    (Construction.lift (F ⋙ W.Q) hF ⋙ Construction.lift (G ⋙ W.Q) hG) (Iso.refl _)

end CategoryTheory.Localization
