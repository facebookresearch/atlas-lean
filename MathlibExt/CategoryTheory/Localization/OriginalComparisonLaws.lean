/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Localization.OriginalComparison

set_option autoImplicit false
noncomputable section
universe u v u' v' uH vH
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {H : Type uH} [Category.{vH} H]

/-- The full projected original comparison keeps its source and target equality transports. -/
theorem originalComparisonIso_hom_projected (W : MorphismProperty C) (P : D ⥤ H)
    {F G : C ⥤ D} (c : F ≅ G) (FH GH : W.Localization ⥤ H)
    (hF : W.Q ⋙ FH = F ⋙ P) (hG : W.Q ⋙ GH = G ⋙ P) (X : C) :
    (originalComparisonIso W P c FH GH hF hG).hom.app (W.Q.obj X) =
      (eqToIso hF).hom.app X ≫ (P.map (c.hom.app X) ≫ (eqToIso hG).inv.app X) := by
  rw [originalComparisonIso, liftNatIso_hom, liftNatTrans_app]
  rfl

/-- The full projected inverse comparison retains the opposite original equality transports. -/
theorem originalComparisonIso_inv_projected (W : MorphismProperty C) (P : D ⥤ H)
    {F G : C ⥤ D} (c : F ≅ G) (FH GH : W.Localization ⥤ H)
    (hF : W.Q ⋙ FH = F ⋙ P) (hG : W.Q ⋙ GH = G ⋙ P) (X : C) :
    (originalComparisonIso W P c FH GH hF hG).inv.app (W.Q.obj X) =
      (eqToIso hG).hom.app X ≫ (P.map (c.inv.app X) ≫ (eqToIso hF).inv.app X) := by
  rw [originalComparisonIso, liftNatIso_inv, liftNatTrans_app]
  rfl

end CategoryTheory.Localization
