/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.CategoryTheory.Localization.Predicate

set_option autoImplicit false
noncomputable section
universe u v u' v' uH vH
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {H : Type uH} [Category.{vH} H]

/-- An actual original raw comparison lifts through the full given projected source functors. -/
def originalComparisonIso (W : MorphismProperty C) (P : D ⥤ H)
    {F G : C ⥤ D} (c : F ≅ G) (FH GH : W.Localization ⥤ H)
    (hF : W.Q ⋙ FH = F ⋙ P) (hG : W.Q ⋙ GH = G ⋙ P) : FH ≅ GH := by
  let _ : Lifting W.Q W (F ⋙ P) FH := ⟨eqToIso hF⟩
  let _ : Lifting W.Q W (G ⋙ P) GH := ⟨eqToIso hG⟩
  exact liftNatIso W.Q W (F ⋙ P) (G ⋙ P) FH GH (Functor.isoWhiskerRight c P)

end CategoryTheory.Localization
