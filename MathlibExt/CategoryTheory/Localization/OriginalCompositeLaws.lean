/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Localization.OriginalComposite

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C]

/-- The named/composite Ho comparison is the original identity on each projected source object. -/
theorem originalCompositeIso_hom_projected (W : MorphismProperty C) (F G : C ⥤ C)
    (hF : W.IsInvertedBy (F ⋙ W.Q)) (hG : W.IsInvertedBy (G ⋙ W.Q))
    (hFG : W.IsInvertedBy ((F ⋙ G) ⋙ W.Q)) (X : C) :
    (originalCompositeIso W F G hF hG hFG).hom.app (W.Q.obj X) =
      𝟙 (W.Q.obj (G.obj (F.obj X))) := by
  rw [originalCompositeIso, liftNatIso_hom, liftNatTrans_app]
  change (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

/-- The inverse named/composite Ho comparison retains that same original identity component. -/
theorem originalCompositeIso_inv_projected (W : MorphismProperty C) (F G : C ⥤ C)
    (hF : W.IsInvertedBy (F ⋙ W.Q)) (hG : W.IsInvertedBy (G ⋙ W.Q))
    (hFG : W.IsInvertedBy ((F ⋙ G) ⋙ W.Q)) (X : C) :
    (originalCompositeIso W F G hF hG hFG).inv.app (W.Q.obj X) =
      𝟙 (W.Q.obj (G.obj (F.obj X))) := by
  rw [originalCompositeIso, liftNatIso_inv, liftNatTrans_app]
  change (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  exact (congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

end CategoryTheory.Localization
