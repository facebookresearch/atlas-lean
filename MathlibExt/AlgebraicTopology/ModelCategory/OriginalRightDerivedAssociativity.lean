/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence

/-!
# Associativity of the original right-derived replacement maps

Both routes retain the same intermediate R units and original right
functor maps. Their equality is the actual unit naturality square before
source localization. No compositor or coherence equality is a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uC uD uE uF vC vD vE vF
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.Functor

namespace HomotopicalAlgebra.OriginalRightDerivedAssociativity

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {F : Type uF} [Category.{vF} F] [ModelCategory F]
  (R : D ⥤ C) (S : E ⥤ D) (T : F ⥤ E)
  (rD : GeneratedFunctorialReplacements.Data (C := D))
  (rE : GeneratedFunctorialReplacements.Data (C := E))
  (rF : GeneratedFunctorialReplacements.Data (C := F))

/-- The two complete intermediate-unit words agree by the original rD naturality. -/
theorem raw_associativity (X : F) :
    (DerivedFunctorCoherence.projection C).map
        (R.map (S.map (rE.r.app (T.obj (rF.R.obj X))))) ≫
      (DerivedFunctorCoherence.projection C).map
        (R.map (rD.r.app (S.obj (rE.R.obj (T.obj (rF.R.obj X)))))) =
      (DerivedFunctorCoherence.projection C).map
          (R.map (rD.r.app (S.obj (T.obj (rF.R.obj X))))) ≫
        (DerivedFunctorCoherence.projection C).map
          (R.map (rD.R.map (S.map (rE.r.app (T.obj (rF.R.obj X)))))) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply (DerivedFunctorCoherence.projection C).congr_map
  apply R.congr_map
  exact rD.r.naturality (S.map (rE.r.app (T.obj (rF.R.obj X))))

section Derived

variable {L : C ⥤ D} {M : D ⥤ E} {N : E ⥤ F}
  (a : L ⊣ R) [a.IsQuillenAdjunction]
  (b : M ⊣ S) [b.IsQuillenAdjunction]
  (c : N ⊣ T) [c.IsQuillenAdjunction]

open DerivedFunctorCoherence

/-- The two original right-derived compositor routes agree on every localized object and arrow. -/
theorem composition_associativity :
    (rightCompositionIso (a.comp b) c rE rF).hom ≫
        whiskerLeft (right c rF) (rightCompositionIso a b rD rE).hom =
      (rightCompositionIso a (b.comp c) rD rF).hom ≫
        whiskerRight (rightCompositionIso b c rE rF).hom (right a rD) := by
  apply Localization.natTrans_ext (projection F) (weakEquivalences F)
  intro X
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  change (rightCompositionIso (a.comp b) c rE rF).hom.app ((projection F).obj X) ≫
      (rightCompositionIso a b rD rE).hom.app ((projection E).obj (T.obj (rF.R.obj X))) =
    (rightCompositionIso a (b.comp c) rD rF).hom.app ((projection F).obj X) ≫
      (right a rD).map ((rightCompositionIso b c rE rF).hom.app ((projection F).obj X))
  rw [rightCompositionIso_app, rightCompositionIso_app, rightCompositionIso_app,
    rightCompositionIso_app]
  erw [right_map a rD (S.map (rE.r.app (T.obj (rF.R.obj X))))]
  change (projection C).map (R.map (S.map (rE.r.app (T.obj (rF.R.obj X))))) ≫
      (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj (T.obj (rF.R.obj X)))))) =
    (projection C).map (R.map (rD.r.app (S.obj (T.obj (rF.R.obj X))))) ≫
      (projection C).map (R.map (rD.R.map (S.map (rE.r.app (T.obj (rF.R.obj X))))))
  exact raw_associativity R S T rD rE rF X

end Derived

end HomotopicalAlgebra.OriginalRightDerivedAssociativity
